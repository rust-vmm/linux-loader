/* SPDX-License-Identifier: MIT */
/*
 * Minimal start_info.h for linux-loader
 * From Linux kernel (commit 48b1320a674e1ff5de2fad8606bee38f724594dc)
 * include/xen/interface/hvm/start_info.h
 */

#ifndef __XEN_PUBLIC_ARCH_X86_HVM_START_INFO_H__
#define __XEN_PUBLIC_ARCH_X86_HVM_START_INFO_H__

/* Basic types */
typedef signed char __s8;
typedef unsigned char __u8;
typedef signed short __s16;
typedef unsigned short __u16;
typedef signed int __s32;
typedef unsigned int __u32;
typedef signed long long __s64;
typedef unsigned long long __u64;

#define XEN_HVM_START_MAGIC_VALUE 0x336ec578

/* Memory map types */
#define XEN_HVM_MEMMAP_TYPE_RAM       1
#define XEN_HVM_MEMMAP_TYPE_RESERVED  2
#define XEN_HVM_MEMMAP_TYPE_ACPI      3
#define XEN_HVM_MEMMAP_TYPE_NVS       4
#define XEN_HVM_MEMMAP_TYPE_UNUSABLE  5
#define XEN_HVM_MEMMAP_TYPE_DISABLED  6
#define XEN_HVM_MEMMAP_TYPE_PMEM      7

/* Start of day structure for PVH boot */
struct hvm_start_info {
	__u32 magic;             /* XEN_HVM_START_MAGIC_VALUE */
	__u32 version;           /* Version of this structure */
	__u32 flags;             /* SIF_xxx flags */
	__u32 nr_modules;        /* Number of modules */
	__u64 modlist_paddr;     /* Physical address of module list */
	__u64 cmdline_paddr;     /* Physical address of command line */
	__u64 rsdp_paddr;        /* Physical address of RSDP ACPI */
	__u64 memmap_paddr;      /* Physical address of memory map */
	__u32 memmap_entries;    /* Number of memory map entries */
	__u32 reserved;          /* Must be zero */
};

/* Module list entry */
struct hvm_modlist_entry {
	__u64 paddr;             /* Physical address of module */
	__u64 size;              /* Size in bytes */
	__u64 cmdline_paddr;     /* Physical address of command line */
	__u64 reserved;          /* Must be zero */
};

/* Memory map entry */
struct hvm_memmap_table_entry {
	__u64 addr;              /* Base address */
	__u64 size;              /* Size in bytes */
	__u32 type;              /* XEN_HVM_MEMMAP_TYPE_* */
	__u32 reserved;          /* Must be zero */
};

#endif /* __XEN_PUBLIC_ARCH_X86_HVM_START_INFO_H__ */
