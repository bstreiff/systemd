/* SPDX-License-Identifier: LGPL-2.1-or-later */

/*
 * Predictable network interface device names based on:
 *  - firmware/bios-provided index numbers for on-board devices
 *  - firmware-provided pci-express hotplug slot index number
 *  - physical/geographical location of the hardware
 *  - the interface's MAC address
 *
 * https://systemd.io/PREDICTABLE_INTERFACE_NAMES
 *
 * When the code here is changed, man/systemd.net-naming-scheme.xml must be updated too.
 */

#include <errno.h>
#include <fcntl.h>
#include <net/if.h>
#include <net/if_arp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>
#include <linux/if.h>
#include <linux/pci_regs.h>

#include "alloc-util.h"
#include "dirent-util.h"
#include "fd-util.h"
#include "fileio.h"
#include "fs-util.h"
#include "netif-naming-scheme.h"
#include "parse-util.h"
#include "proc-cmdline.h"
#include "stdio-util.h"
#include "string-util.h"
#include "strv.h"
#include "strxcpyx.h"
#include "udev-builtin.h"

#define ONBOARD_INDEX_MAX (16*1024-1)

enum netname_type{
        NET_UNDEF,
        NET_ACPI,
        NET_PCI,
        NET_USB,
        NET_BCMA,
        NET_VIRTIO,
        NET_CCW,
        NET_VIO,
        NET_PLATFORM,
};

struct netnames {
        enum netname_type type;

        char acpi_index[ALTIFNAMSIZ];
        char acpi_label[ALTIFNAMSIZ];

        sd_device *pcidev;
        char pci_slot[ALTIFNAMSIZ];
        char pci_path[ALTIFNAMSIZ];
        char pci_onboard[ALTIFNAMSIZ];
        const char *pci_onboard_label;

        char usb_ports[ALTIFNAMSIZ];
        char bcma_core[ALTIFNAMSIZ];
        char ccw_busid[ALTIFNAMSIZ];
        char vio_slot[ALTIFNAMSIZ];
        char platform_path[ALTIFNAMSIZ];
        char netdevsim_path[ALTIFNAMSIZ];
};

struct virtfn_info {
        sd_device *physfn_pcidev;
        char suffix[ALTIFNAMSIZ];
};

/* skip intermediate virtio devices */
static sd_device *skip_virtio(sd_device *dev) {
        sd_device *parent;

        /* there can only ever be one virtio bus per parent device, so we can
         * safely ignore any virtio buses. see
         * http://lists.linuxfoundation.org/pipermail/virtualization/2015-August/030331.html */
        for (parent = dev; parent; ) {
                const char *subsystem;

                if (sd_device_get_subsystem(parent, &subsystem) < 0)
                        break;

                if (!streq(subsystem, "virtio"))
                        break;

                if (sd_device_get_parent(parent, &parent) < 0)
                        return NULL;
        }

        return parent;
}

static int get_virtfn_info(sd_device *dev, struct netnames *names, struct virtfn_info *ret) {
        _cleanup_(sd_device_unrefp) sd_device *physfn_pcidev = NULL;
        const char *physfn_link_file, *syspath;
        _cleanup_free_ char *physfn_pci_syspath = NULL;
        _cleanup_free_ char *virtfn_pci_syspath = NULL;
        struct dirent *dent;
        _cleanup_closedir_ DIR *dir = NULL;
        char suffix[ALTIFNAMSIZ];
        int r;

        assert(dev);
        assert(names);
        assert(ret);

        r = sd_device_get_syspath(names->pcidev, &syspath);
        if (r < 0)
                return r;

        /* Check if this is a virtual function. */
        physfn_link_file = strjoina(syspath, "/physfn");
        r = chase_symlinks(physfn_link_file, NULL, 0, &physfn_pci_syspath, NULL);
        if (r < 0)
                return r;

        /* Get physical function's pci device. */
        r = sd_device_new_from_syspath(&physfn_pcidev, physfn_pci_syspath);
        if (r < 0)
                return r;

        /* Find the virtual function number by finding the right virtfn link. */
        dir = opendir(physfn_pci_syspath);
        if (!dir)
                return -errno;

        FOREACH_DIRENT_ALL(dent, dir, break) {
                _cleanup_free_ char *virtfn_link_file = NULL;

                if (!startswith(dent->d_name, "virtfn"))
                        continue;

                virtfn_link_file = path_join(physfn_pci_syspath, dent->d_name);
                if (!virtfn_link_file)
                        return -ENOMEM;

                if (chase_symlinks(virtfn_link_file, NULL, 0, &virtfn_pci_syspath, NULL) < 0)
                        continue;

                if (streq(syspath, virtfn_pci_syspath)) {
                        if (!snprintf_ok(suffix, sizeof(suffix), "v%s", &dent->d_name[6]))
                                return -ENOENT;

                        break;
                }
        }
        if (isempty(suffix))
                return -ENOENT;

        ret->physfn_pcidev = TAKE_PTR(physfn_pcidev);
        strncpy(ret->suffix, suffix, sizeof(ret->suffix));

        return 0;
}

/* for devices on non-enumerable buses (e.g. ISA) that have ACPI tables */
static int dev_acpi_firmware(sd_device *dev, struct netnames *names) {
        unsigned long idx;
        const char *attr;
        const char *subsystem;
        const char *uid_str = NULL;
        sd_device *parent;
        size_t l;
        char *s;
        int r;

        /* check if our direct parent is a VIO device with no other bus in-between */
        r = sd_device_get_parent(dev, &parent);
        if (r < 0)
                return r;

        r = sd_device_get_subsystem(parent, &subsystem);
        if (r < 0)
                return r;

        /* ACPI _HID is required, although we don't use it */
        if (sd_device_get_sysattr_value(parent, "firmware_node/hid", &attr) < 0) {
                return -ENOENT;
        }

        /* ACPI _UID - may be an integer or a string */
        if (sd_device_get_sysattr_value(parent, "firmware_node/uid", &attr) == 0) {
                r = safe_atolu(attr, &idx);
                if (r < 0) {
                        /* if it's not an integer, treat it as a string */
                        uid_str = attr;
                        idx = ONBOARD_INDEX_MAX+1;
                }
        }

        s = names->acpi_label;
        l = sizeof(names->acpi_label);

        if (sd_device_get_sysattr_value(parent, "firmware_node/description", &attr) == 0) {
                /* ACPI _STR - descriptive string */
                strscpy(s, l, attr);
        } else if (sd_device_get_sysattr_value(parent, "firmware_node/ddn", &attr) == 0) {
                /* ACPI _DDN - DOS device name */
                strscpy(s, l, attr);
        } else if (uid_str) {
                /* ACPI _UID if a string */
                strscpy(s, l, uid_str);
        } else if (idx <= ONBOARD_INDEX_MAX) {
                /* ACPI _UID if a valid index number, expressed as if it were a DOS COM device */
                strpcpyf(&s, l, "COM%lu", idx);
        }

        names->type = NET_ACPI;
        return 0;
}

/* retrieve on-board index number and label from firmware */
static int dev_pci_onboard(sd_device *dev, struct netnames *names) {
        unsigned long idx, dev_port = 0;
        const char *attr, *port_name = NULL;
        size_t l;
        char *s;
        int r;

        /* ACPI _DSM — device specific method for naming a PCI or PCI Express device */
        if (sd_device_get_sysattr_value(names->pcidev, "acpi_index", &attr) < 0) {
                /* SMBIOS type 41 — Onboard Devices Extended Information */
                r = sd_device_get_sysattr_value(names->pcidev, "index", &attr);
                if (r < 0)
                        return r;
        }

        r = safe_atolu(attr, &idx);
        if (r < 0)
                return r;
        if (idx == 0 && !naming_scheme_has(NAMING_ZERO_ACPI_INDEX))
                return -EINVAL;

        /* Some BIOSes report rubbish indexes that are excessively high (2^24-1 is an index VMware likes to
         * report for example). Let's define a cut-off where we don't consider the index reliable anymore. We
         * pick some arbitrary cut-off, which is somewhere beyond the realistic number of physical network
         * interface a system might have. Ideally the kernel would already filter this crap for us, but it
         * doesn't currently. */
        if (idx > ONBOARD_INDEX_MAX)
                return -ENOENT;

        /* kernel provided port index for multiple ports on a single PCI function */
        if (sd_device_get_sysattr_value(dev, "dev_port", &attr) >= 0)
                dev_port = strtoul(attr, NULL, 10);

        /* kernel provided front panel port name for multiple port PCI device */
        (void) sd_device_get_sysattr_value(dev, "phys_port_name", &port_name);

        s = names->pci_onboard;
        l = sizeof(names->pci_onboard);
        l = strpcpyf(&s, l, "o%lu", idx);
        if (port_name)
                l = strpcpyf(&s, l, "n%s", port_name);
        else if (dev_port > 0)
                l = strpcpyf(&s, l, "d%lu", dev_port);
        if (l == 0)
                names->pci_onboard[0] = '\0';

        if (sd_device_get_sysattr_value(names->pcidev, "label", &names->pci_onboard_label) < 0)
                names->pci_onboard_label = NULL;

        return 0;
}

/* read the 256 bytes PCI configuration space to check the multi-function bit */
static bool is_pci_multifunction(sd_device *dev) {
        _cleanup_close_ int fd = -1;
        const char *filename, *syspath;
        uint8_t config[64];

        if (sd_device_get_syspath(dev, &syspath) < 0)
                return false;

        filename = strjoina(syspath, "/config");
        fd = open(filename, O_RDONLY | O_CLOEXEC);
        if (fd < 0)
                return false;
        if (read(fd, &config, sizeof(config)) != sizeof(config))
                return false;

        /* bit 0-6 header type, bit 7 multi/single function device */
        return config[PCI_HEADER_TYPE] & 0x80;
}

static bool is_pci_ari_enabled(sd_device *dev) {
        const char *a;

        if (sd_device_get_sysattr_value(dev, "ari_enabled", &a) < 0)
                return false;

        return streq(a, "1");
}

static bool is_pci_bridge(sd_device *dev) {
        const char *v, *p;

        if (sd_device_get_sysattr_value(dev, "modalias", &v) < 0)
                return false;

        if (!startswith(v, "pci:"))
                return false;

        p = strrchr(v, 's');
        if (!p)
                return false;
        if (p[1] != 'c')
                return false;

        /* PCI device subclass 04 corresponds to PCI bridge */
        return strneq(p + 2, "04", 2);
}

static int dev_pci_slot(sd_device *dev, struct netnames *names) {
        unsigned long dev_port = 0;
        unsigned domain, bus, slot, func;
        int hotplug_slot = -1;
        size_t l;
        char *s;
        const char *sysname, *attr, *port_name = NULL, *syspath;
        _cleanup_(sd_device_unrefp) sd_device *pci = NULL;
        sd_device *hotplug_slot_dev;
        char slots[PATH_MAX];
        _cleanup_closedir_ DIR *dir = NULL;
        struct dirent *dent;
        int r;

        r = sd_device_get_sysname(names->pcidev, &sysname);
        if (r < 0)
                return r;

        if (sscanf(sysname, "%x:%x:%x.%u", &domain, &bus, &slot, &func) != 4)
                return -ENOENT;

        if (naming_scheme_has(NAMING_NPAR_ARI) &&
            is_pci_ari_enabled(names->pcidev))
                /* ARI devices support up to 256 functions on a single device ("slot"), and interpret the
                 * traditional 5-bit slot and 3-bit function number as a single 8-bit function number,
                 * where the slot makes up the upper 5 bits. */
                func += slot * 8;

        /* kernel provided port index for multiple ports on a single PCI function */
        if (sd_device_get_sysattr_value(dev, "dev_port", &attr) >= 0) {
                dev_port = strtoul(attr, NULL, 10);
                /* With older kernels IP-over-InfiniBand network interfaces sometimes erroneously
                 * provide the port number in the 'dev_id' sysfs attribute instead of 'dev_port',
                 * which thus stays initialized as 0. */
                if (dev_port == 0 &&
                    sd_device_get_sysattr_value(dev, "type", &attr) >= 0) {
                        unsigned long type;

                        type = strtoul(attr, NULL, 10);
                        if (type == ARPHRD_INFINIBAND &&
                            sd_device_get_sysattr_value(dev, "dev_id", &attr) >= 0)
                                dev_port = strtoul(attr, NULL, 16);
                }
        }

        /* kernel provided front panel port name for multi-port PCI device */
        (void) sd_device_get_sysattr_value(dev, "phys_port_name", &port_name);

        /* compose a name based on the raw kernel's PCI bus, slot numbers */
        s = names->pci_path;
        l = sizeof(names->pci_path);
        if (domain > 0)
                l = strpcpyf(&s, l, "P%u", domain);
        l = strpcpyf(&s, l, "p%us%u", bus, slot);
        if (func > 0 || is_pci_multifunction(names->pcidev))
                l = strpcpyf(&s, l, "f%u", func);
        if (port_name)
                l = strpcpyf(&s, l, "n%s", port_name);
        else if (dev_port > 0)
                l = strpcpyf(&s, l, "d%lu", dev_port);
        if (l == 0)
                names->pci_path[0] = '\0';

        /* ACPI _SUN — slot user number */
        r = sd_device_new_from_subsystem_sysname(&pci, "subsystem", "pci");
        if (r < 0)
                return r;

        r = sd_device_get_syspath(pci, &syspath);
        if (r < 0)
                return r;
        if (!snprintf_ok(slots, sizeof slots, "%s/slots", syspath))
                return -ENAMETOOLONG;

        dir = opendir(slots);
        if (!dir)
                return -errno;

        hotplug_slot_dev = names->pcidev;
        while (hotplug_slot_dev) {
                if (sd_device_get_sysname(hotplug_slot_dev, &sysname) < 0)
                        continue;

                FOREACH_DIRENT_ALL(dent, dir, break) {
                        int i;
                        char str[PATH_MAX];
                        _cleanup_free_ char *address = NULL;

                        if (dot_or_dot_dot(dent->d_name))
                                continue;

                        r = safe_atoi(dent->d_name, &i);
                        if (r < 0 || i <= 0)
                                continue;

                        /* match slot address with device by stripping the function */
                        if (snprintf_ok(str, sizeof str, "%s/%s/address", slots, dent->d_name) &&
                            read_one_line_file(str, &address) >= 0 &&
                            startswith(sysname, address)) {
                                hotplug_slot = i;

                                /* We found the match between PCI device and slot. However, we won't use the
                                 * slot index if the device is a PCI bridge, because it can have other child
                                 * devices that will try to claim the same index and that would create name
                                 * collision. */
                                if (naming_scheme_has(NAMING_BRIDGE_NO_SLOT) && is_pci_bridge(hotplug_slot_dev))
                                        hotplug_slot = 0;

                                break;
                        }
                }
                if (hotplug_slot >= 0)
                        break;
                if (sd_device_get_parent_with_subsystem_devtype(hotplug_slot_dev, "pci", NULL, &hotplug_slot_dev) < 0)
                        break;
                rewinddir(dir);
        }

        if (hotplug_slot > 0) {
                s = names->pci_slot;
                l = sizeof(names->pci_slot);
                if (domain > 0)
                        l = strpcpyf(&s, l, "P%d", domain);
                l = strpcpyf(&s, l, "s%d", hotplug_slot);
                if (func > 0 || is_pci_multifunction(names->pcidev))
                        l = strpcpyf(&s, l, "f%d", func);
                if (port_name)
                        l = strpcpyf(&s, l, "n%s", port_name);
                else if (dev_port > 0)
                        l = strpcpyf(&s, l, "d%lu", dev_port);
                if (l == 0)
                        names->pci_slot[0] = '\0';
        }

        return 0;
}

static int names_vio(sd_device *dev, struct netnames *names) {
        sd_device *parent;
        unsigned busid, slotid, ethid;
        const char *syspath, *subsystem;
        int r;

        /* check if our direct parent is a VIO device with no other bus in-between */
        r = sd_device_get_parent(dev, &parent);
        if (r < 0)
                return r;

        r = sd_device_get_subsystem(parent, &subsystem);
        if (r < 0)
                return r;
        if (!streq("vio", subsystem))
                return -ENOENT;

        /* The devices' $DEVPATH number is tied to (virtual) hardware (slot id
         * selected in the HMC), thus this provides a reliable naming (e.g.
         * "/devices/vio/30000002/net/eth1"); we ignore the bus number, as
         * there should only ever be one bus, and then remove leading zeros. */
        r = sd_device_get_syspath(dev, &syspath);
        if (r < 0)
                return r;

        if (sscanf(syspath, "/sys/devices/vio/%4x%4x/net/eth%u", &busid, &slotid, &ethid) != 3)
                return -EINVAL;

        xsprintf(names->vio_slot, "v%u", slotid);
        names->type = NET_VIO;
        return 0;
}

#define _PLATFORM_TEST "/sys/devices/platform/vvvvPPPP"
#define _PLATFORM_PATTERN4 "/sys/devices/platform/%4s%4x:%2x/net/eth%u"
#define _PLATFORM_PATTERN3 "/sys/devices/platform/%3s%4x:%2x/net/eth%u"

static int names_platform(sd_device *dev, struct netnames *names, bool test) {
        sd_device *parent;
        char vendor[5];
        unsigned model, instance, ethid;
        const char *syspath, *pattern, *validchars, *subsystem;
        int r;

        /* check if our direct parent is a platform device with no other bus in-between */
        r = sd_device_get_parent(dev, &parent);
        if (r < 0)
                return r;

        r = sd_device_get_subsystem(parent, &subsystem);
        if (r < 0)
                return r;

        if (!streq("platform", subsystem))
                 return -ENOENT;

        r = sd_device_get_syspath(dev, &syspath);
        if (r < 0)
                return r;

        /* syspath is too short, to have a valid ACPI instance */
        if (strlen(syspath) < sizeof _PLATFORM_TEST)
                return -EINVAL;

        /* Vendor ID can be either PNP ID (3 chars A-Z) or ACPI ID (4 chars A-Z and numerals) */
        if (syspath[sizeof _PLATFORM_TEST - 1] == ':') {
                pattern = _PLATFORM_PATTERN4;
                validchars = UPPERCASE_LETTERS DIGITS;
        } else {
                pattern = _PLATFORM_PATTERN3;
                validchars = UPPERCASE_LETTERS;
        }

        /* Platform devices are named after ACPI table match, and instance id
         * eg. "/sys/devices/platform/HISI00C2:00");
         * The Vendor (3 or 4 char), followed by hexdecimal model number : instance id.
         */

        DISABLE_WARNING_FORMAT_NONLITERAL;
        if (sscanf(syspath, pattern, vendor, &model, &instance, &ethid) != 4)
                return -EINVAL;
        REENABLE_WARNING;

        if (!in_charset(vendor, validchars))
                return -ENOENT;

        ascii_strlower(vendor);

        xsprintf(names->platform_path, "a%s%xi%u", vendor, model, instance);
        names->type = NET_PLATFORM;
        return 0;
}

static int names_pci(sd_device *dev, struct netnames *names) {
        sd_device *parent;
        struct netnames vf_names = {};
        struct virtfn_info vf_info = {};
        const char *subsystem;
        int r;

        assert(dev);
        assert(names);

        r = sd_device_get_parent(dev, &parent);
        if (r < 0)
                return r;
        /* skip virtio subsystem if present */
        parent = skip_virtio(parent);

        if (!parent)
                return -ENOENT;

        /* check if our direct parent is a PCI device with no other bus in-between */
        if (sd_device_get_subsystem(parent, &subsystem) >= 0 &&
            streq("pci", subsystem)) {
                names->type = NET_PCI;
                names->pcidev = parent;
        } else {
                r = sd_device_get_parent_with_subsystem_devtype(dev, "pci", NULL, &names->pcidev);
                if (r < 0)
                        return r;
        }

        if (naming_scheme_has(NAMING_SR_IOV_V) &&
            get_virtfn_info(dev, names, &vf_info) >= 0) {
                /* If this is an SR-IOV virtual device, get base name using physical device and add virtfn suffix. */
                vf_names.pcidev = vf_info.physfn_pcidev;
                dev_pci_onboard(dev, &vf_names);
                dev_pci_slot(dev, &vf_names);
                if (vf_names.pci_onboard[0])
                        if (strlen(vf_names.pci_onboard) + strlen(vf_info.suffix) < sizeof(names->pci_onboard))
                                strscpyl(names->pci_onboard, sizeof(names->pci_onboard),
                                         vf_names.pci_onboard, vf_info.suffix, NULL);
                if (vf_names.pci_slot[0])
                        if (strlen(vf_names.pci_slot) + strlen(vf_info.suffix) < sizeof(names->pci_slot))
                                strscpyl(names->pci_slot, sizeof(names->pci_slot),
                                         vf_names.pci_slot, vf_info.suffix, NULL);
                if (vf_names.pci_path[0])
                        if (strlen(vf_names.pci_path) + strlen(vf_info.suffix) < sizeof(names->pci_path))
                                strscpyl(names->pci_path, sizeof(names->pci_path),
                                         vf_names.pci_path, vf_info.suffix, NULL);
                sd_device_unref(vf_info.physfn_pcidev);
        } else {
                dev_pci_onboard(dev, names);
                dev_pci_slot(dev, names);
        }

        return 0;
}

static int names_usb(sd_device *dev, struct netnames *names) {
        sd_device *usbdev;
        char name[256], *ports, *config, *interf, *s;
        const char *sysname;
        size_t l;
        int r;

        assert(dev);
        assert(names);

        r = sd_device_get_parent_with_subsystem_devtype(dev, "usb", "usb_interface", &usbdev);
        if (r < 0)
                return r;

        r = sd_device_get_sysname(usbdev, &sysname);
        if (r < 0)
                return r;

        /* get USB port number chain, configuration, interface */
        strscpy(name, sizeof(name), sysname);
        s = strchr(name, '-');
        if (!s)
                return -EINVAL;
        ports = s+1;

        s = strchr(ports, ':');
        if (!s)
                return -EINVAL;
        s[0] = '\0';
        config = s+1;

        s = strchr(config, '.');
        if (!s)
                return -EINVAL;
        s[0] = '\0';
        interf = s+1;

        /* prefix every port number in the chain with "u" */
        s = ports;
        while ((s = strchr(s, '.')))
                s[0] = 'u';
        s = names->usb_ports;
        l = strpcpyl(&s, sizeof(names->usb_ports), "u", ports, NULL);

        /* append USB config number, suppress the common config == 1 */
        if (!streq(config, "1"))
                l = strpcpyl(&s, sizeof(names->usb_ports), "c", config, NULL);

        /* append USB interface number, suppress the interface == 0 */
        if (!streq(interf, "0"))
                l = strpcpyl(&s, sizeof(names->usb_ports), "i", interf, NULL);
        if (l == 0)
                return -ENAMETOOLONG;

        names->type = NET_USB;
        return 0;
}

static int names_bcma(sd_device *dev, struct netnames *names) {
        sd_device *bcmadev;
        unsigned core;
        const char *sysname;
        int r;

        assert(dev);
        assert(names);

        r = sd_device_get_parent_with_subsystem_devtype(dev, "bcma", NULL, &bcmadev);
        if (r < 0)
                return r;

        r = sd_device_get_sysname(bcmadev, &sysname);
        if (r < 0)
                return r;

        /* bus num:core num */
        if (sscanf(sysname, "bcma%*u:%u", &core) != 1)
                return -EINVAL;
        /* suppress the common core == 0 */
        if (core > 0)
                xsprintf(names->bcma_core, "b%u", core);

        names->type = NET_BCMA;
        return 0;
}

static int names_ccw(sd_device *dev, struct netnames *names) {
        sd_device *cdev;
        const char *bus_id, *subsys;
        size_t bus_id_len;
        size_t bus_id_start;
        int r;

        assert(dev);
        assert(names);

        /* Retrieve the associated CCW device */
        r = sd_device_get_parent(dev, &cdev);
        if (r < 0)
                return r;

        /* skip virtio subsystem if present */
        cdev = skip_virtio(cdev);
        if (!cdev)
                return -ENOENT;

        r = sd_device_get_subsystem(cdev, &subsys);
        if (r < 0)
                return r;

        /* Network devices are either single or grouped CCW devices */
        if (!STR_IN_SET(subsys, "ccwgroup", "ccw"))
                return -ENOENT;

        /* Retrieve bus-ID of the CCW device.  The bus-ID uniquely
         * identifies the network device on the Linux on System z channel
         * subsystem.  Note that the bus-ID contains lowercase characters.
         */
        r = sd_device_get_sysname(cdev, &bus_id);
        if (r < 0)
                return r;

        /* Check the length of the bus-ID. Rely on the fact that the kernel provides a correct bus-ID;
         * alternatively, improve this check and parse and verify each bus-ID part...
         */
        bus_id_len = strlen(bus_id);
        if (!IN_SET(bus_id_len, 8, 9))
                return -EINVAL;

        /* Strip leading zeros from the bus id for aesthetic purposes. This
         * keeps the ccw names stable, yet much shorter in general case of
         * bus_id 0.0.0600 -> 600. This is similar to e.g. how PCI domain is
         * not prepended when it is zero. Preserve the last 0 for 0.0.0000.
         */
        bus_id_start = strspn(bus_id, ".0");
        bus_id += bus_id_start < bus_id_len ? bus_id_start : bus_id_len - 1;

        /* Store the CCW bus-ID for use as network device name */
        if (snprintf_ok(names->ccw_busid, sizeof(names->ccw_busid), "c%s", bus_id))
                names->type = NET_CCW;

        return 0;
}

static int builtin_serial_id(sd_device *dev, int argc, char *argv[], bool test) {
        const char *prefix = "en";
        struct netnames names = {};

        udev_builtin_add_property(dev, test, "ID_SERIAL_NAMING_SCHEME", naming_scheme()->name);

        if (dev_acpi_firmware(dev, &names) >= 0 && names.type == NET_ACPI) {
                udev_builtin_add_property(dev, test, "ID_SERIAL_LABEL", names.acpi_label);
                return 0;
        }

        /* get path names for Linux on System z network devices */
        if (names_ccw(dev, &names) >= 0 && names.type == NET_CCW) {
                char str[ALTIFNAMSIZ];

                if (snprintf_ok(str, sizeof str, "%s%s", prefix, names.ccw_busid))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_PATH", str);
                return 0;
        }

        /* get ibmveth/ibmvnic slot-based names. */
        if (names_vio(dev, &names) >= 0 && names.type == NET_VIO) {
                char str[ALTIFNAMSIZ];

                if (snprintf_ok(str, sizeof str, "%s%s", prefix, names.vio_slot))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_SLOT", str);
                return 0;
        }

        /* get ACPI path names for ARM64 platform devices */
        if (names_platform(dev, &names, test) >= 0 && names.type == NET_PLATFORM) {
                char str[ALTIFNAMSIZ];

                if (snprintf_ok(str, sizeof str, "%s%s", prefix, names.platform_path))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_PATH", str);
                return 0;
        }

        /* get PCI based path names, we compose only PCI based paths */
        if (names_pci(dev, &names) < 0)
                return 0;

        /* plain PCI device */
        if (names.type == NET_PCI) {
                if (names.pci_onboard[0])
                        udev_builtin_add_property(dev, test, "ID_SERIAL_NAME_ONBOARD", names.pci_onboard);

                if (names.pci_onboard_label)
                        udev_builtin_add_property(dev, test, "ID_SERIAL_LABEL_ONBOARD", names.pci_onboard_label);

                if (names.pci_path[0])
                        udev_builtin_add_property(dev, test, "ID_SERIAL_NAME_PATH", names.pci_path);

                if (names.pci_slot[0])
                        udev_builtin_add_property(dev, test, "ID_SERIAL_NAME_SLOT", names.pci_slot);
                return 0;
        }

        /* USB device */
        if (names_usb(dev, &names) >= 0 && names.type == NET_USB) {
                char str[ALTIFNAMSIZ];

                if (names.pci_path[0] &&
                    snprintf_ok(str, sizeof str, "%s%s%s", prefix, names.pci_path, names.usb_ports))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_PATH", str);

                if (names.pci_slot[0] &&
                    snprintf_ok(str, sizeof str, "%s%s%s", prefix, names.pci_slot, names.usb_ports))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_SLOT", str);
                return 0;
        }

        /* Broadcom bus */
        if (names_bcma(dev, &names) >= 0 && names.type == NET_BCMA) {
                char str[ALTIFNAMSIZ];

                if (names.pci_path[0] &&
                    snprintf_ok(str, sizeof str, "%s%s%s", prefix, names.pci_path, names.bcma_core))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_PATH", str);

                if (names.pci_slot[0] &&
                    snprintf(str, sizeof str, "%s%s%s", prefix, names.pci_slot, names.bcma_core))
                        udev_builtin_add_property(dev, test, "ID_NET_NAME_SLOT", str);
                return 0;
        }

        return 0;
}

const UdevBuiltin udev_builtin_serial_id = {
        .name = "serial_id",
        .cmd = builtin_serial_id,
        .help = "Serial device properties",
};
