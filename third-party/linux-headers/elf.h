/* SPDX-License-Identifier: GPL-2.0 WITH Linux-syscall-note */
/*
 * Minimal elf.h for linux-loader
 * From Linux kernel (commit 48b1320a674e1ff5de2fad8606bee38f724594dc)
 * include/uapi/linux/elf.h
 */

#ifndef _UAPI_LINUX_ELF_H
#define _UAPI_LINUX_ELF_H

/* Basic kernel types */
typedef signed char __s8;
typedef unsigned char __u8;
typedef signed short __s16;
typedef unsigned short __u16;
typedef signed int __s32;
typedef unsigned int __u32;
typedef signed long long __s64;
typedef unsigned long long __u64;

/* ELF magic number components */
#define ELFMAG0		0x7f
#define ELFMAG1		'E'
#define ELFMAG2		'L'
#define ELFMAG3		'F'

/* ELF header e_ident[] indices */
#define EI_MAG0		0
#define EI_MAG1		1
#define EI_MAG2		2
#define EI_MAG3		3
#define EI_CLASS	4
#define EI_DATA		5
#define EI_VERSION	6
#define EI_OSABI	7
#define EI_PAD		8

/* ELF data encoding */
#define ELFDATA2LSB	1  /* Little endian */

/* Program segment types */
#define PT_LOAD		1
#define PT_NOTE		4

/* 64-bit ELF base types */
typedef __u64	Elf64_Addr;
typedef __u16	Elf64_Half;
typedef __s16	Elf64_SHalf;
typedef __u64	Elf64_Off;
typedef __s32	Elf64_Sword;
typedef __u32	Elf64_Word;
typedef __u64	Elf64_Xword;
typedef __s64	Elf64_Sxword;

/* 64-bit ELF header */
typedef struct elf64_hdr {
  unsigned char	e_ident[16];	/* ELF "magic number" */
  Elf64_Half e_type;
  Elf64_Half e_machine;
  Elf64_Word e_version;
  Elf64_Addr e_entry;		/* Entry point virtual address */
  Elf64_Off e_phoff;		/* Program header table file offset */
  Elf64_Off e_shoff;		/* Section header table file offset */
  Elf64_Word e_flags;
  Elf64_Half e_ehsize;
  Elf64_Half e_phentsize;
  Elf64_Half e_phnum;
  Elf64_Half e_shentsize;
  Elf64_Half e_shnum;
  Elf64_Half e_shstrndx;
} Elf64_Ehdr;

/* 64-bit program header */
typedef struct elf64_phdr {
  Elf64_Word p_type;
  Elf64_Word p_flags;
  Elf64_Off p_offset;		/* Segment file offset */
  Elf64_Addr p_vaddr;		/* Segment virtual address */
  Elf64_Addr p_paddr;		/* Segment physical address */
  Elf64_Xword p_filesz;		/* Segment size in file */
  Elf64_Xword p_memsz;		/* Segment size in memory */
  Elf64_Xword p_align;		/* Segment alignment, file & memory */
} Elf64_Phdr;

/* 64-bit note header */
typedef struct elf64_note {
  Elf64_Word n_namesz;		/* Name size */
  Elf64_Word n_descsz;		/* Content size */
  Elf64_Word n_type;		/* Content type */
} Elf64_Nhdr;

#endif /* _UAPI_LINUX_ELF_H */
