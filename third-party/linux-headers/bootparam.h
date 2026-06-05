/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
/*
 * Minimal bootparam.h for linux-loader
 * From Linux kernel (commit 48b1320a674e1ff5de2fad8606bee38f724594dc)
 * arch/x86/include/uapi/asm/bootparam.h
 *
 * Only includes setup_header and boot_params structures needed by linux-loader.
 * Nested structures are defined with correct sizes/layouts but simplified.
 */

#ifndef _ASM_X86_BOOTPARAM_H
#define _ASM_X86_BOOTPARAM_H

/* Basic kernel types */
typedef signed char __s8;
typedef unsigned char __u8;
typedef signed short __s16;
typedef unsigned short __u16;
typedef signed int __s32;
typedef unsigned int __u32;
typedef signed long long __s64;
typedef unsigned long long __u64;

/* Nested structures (sizes must match original) */
struct screen_info {
	__u8 data[64];  /* Size: 64 bytes */
} __attribute__((packed));

struct apm_bios_info {
	__u16 version;
	__u16 cseg;
	__u32 offset;
	__u16 cseg_16;
	__u16 dseg;
	__u16 flags;
	__u16 cseg_len;
	__u16 cseg_16_len;
	__u16 dseg_len;
};

struct ist_info {
	__u32 signature;
	__u32 command;
	__u32 event;
	__u32 perf_level;
};

struct sys_desc_table {
	__u16 length;
	__u8 table[14];
};

struct olpc_ofw_header {
	__u32 ofw_magic;
	__u32 ofw_version;
	__u32 cif_handler;
	__u32 irq_desc_table;
} __attribute__((packed));

struct edid_info {
	__u8 dummy[128];
};

struct efi_info {
	__u32 efi_loader_signature;
	__u32 efi_systab;
	__u32 efi_memdesc_size;
	__u32 efi_memdesc_version;
	__u32 efi_memmap;
	__u32 efi_memmap_size;
	__u32 efi_systab_hi;
	__u32 efi_memmap_hi;
};

struct boot_e820_entry {
	__u64 addr;
	__u64 size;
	__u32 type;
} __attribute__((packed));

struct edd_info {
	__u8 data[82];  /* Size: 82 bytes */
} __attribute__((packed));

/* setup_header - Boot protocol header */
struct setup_header {
	__u8	setup_sects;
	__u16	root_flags;
	__u32	syssize;
	__u16	ram_size;
	__u16	vid_mode;
	__u16	root_dev;
	__u16	boot_flag;
	__u16	jump;
	__u32	header;
	__u16	version;
	__u32	realmode_swtch;
	__u16	start_sys_seg;
	__u16	kernel_version;
	__u8	type_of_loader;
	__u8	loadflags;
	__u16	setup_move_size;
	__u32	code32_start;
	__u32	ramdisk_image;
	__u32	ramdisk_size;
	__u32	bootsect_kludge;
	__u16	heap_end_ptr;
	__u8	ext_loader_ver;
	__u8	ext_loader_type;
	__u32	cmd_line_ptr;
	__u32	initrd_addr_max;
	__u32	kernel_alignment;
	__u8	relocatable_kernel;
	__u8	min_alignment;
	__u16	xloadflags;
	__u32	cmdline_size;
	__u32	hardware_subarch;
	__u64	hardware_subarch_data;
	__u32	payload_offset;
	__u32	payload_length;
	__u64	setup_data;
	__u64	pref_address;
	__u32	init_size;
	__u32	handover_offset;
	__u32	kernel_info_offset;
} __attribute__((packed));

/* boot_params - Complete boot parameters structure (4096 bytes) */
struct boot_params {
	struct screen_info screen_info;			/* 0x000 */
	struct apm_bios_info apm_bios_info;		/* 0x040 */
	__u8  _pad2[4];					/* 0x054 */
	__u64  tboot_addr;				/* 0x058 */
	struct ist_info ist_info;			/* 0x060 */
	__u64 acpi_rsdp_addr;				/* 0x070 */
	__u8  _pad3[8];					/* 0x078 */
	__u8  hd0_info[16];	/* obsolete! */		/* 0x080 */
	__u8  hd1_info[16];	/* obsolete! */		/* 0x090 */
	struct sys_desc_table sys_desc_table; /* obsolete! */	/* 0x0a0 */
	struct olpc_ofw_header olpc_ofw_header;		/* 0x0b0 */
	__u32 ext_ramdisk_image;			/* 0x0c0 */
	__u32 ext_ramdisk_size;				/* 0x0c4 */
	__u32 ext_cmd_line_ptr;				/* 0x0c8 */
	__u8  _pad4[112];				/* 0x0cc */
	__u32 cc_blob_address;				/* 0x13c */
	struct edid_info edid_info;			/* 0x140 */
	struct efi_info efi_info;			/* 0x1c0 */
	__u32 alt_mem_k;				/* 0x1e0 */
	__u32 scratch;		/* Scratch field! */	/* 0x1e4 */
	__u8  e820_entries;				/* 0x1e8 */
	__u8  eddbuf_entries;				/* 0x1e9 */
	__u8  edd_mbr_sig_buf_entries;			/* 0x1ea */
	__u8  kbd_status;				/* 0x1eb */
	__u8  secure_boot;				/* 0x1ec */
	__u8  _pad5[2];					/* 0x1ed */
	__u8  sentinel;					/* 0x1ef */
	__u8  _pad6[1];					/* 0x1f0 */
	struct setup_header hdr;    /* setup header */	/* 0x1f1 */
	__u8  _pad7[36];				/* 0x268 */
	__u32 edd_mbr_sig_buffer[16];			/* 0x290 */
	struct boot_e820_entry e820_table[128];		/* 0x2d0 */
	__u8  _pad8[48];				/* 0xcd0 */
	struct edd_info eddbuf[6];			/* 0xd00 */
	__u8  _pad9[276];				/* 0xeec */
} __attribute__((packed));				/* 0x1000 total */

#endif /* _ASM_X86_BOOTPARAM_H */
