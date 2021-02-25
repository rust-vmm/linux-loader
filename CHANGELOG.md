# [v0.3.0]

## Fixed

- Replaced panic condition in `align_up` with returning an Error.
- Fixed potential hang condition in Elf::load caused by arithmetic overflow.
- Disallow overflow when computing the kernel load address when loading ELF.
- Fix unchecked arithmetic in BzImage::load that could lead to undefined
  behavior.


## Added

- Added functions for specifying virtio MMIO devices when building the kernel
  command line.
- Added a function to specify multiple values in `key=values` pairs when
  building the kernel command line.

# [v0.2.0]

## Added

- Added traits and structs for loading ELF (`vmlinux`), big zImage (`bzImage`)
  and PE (`Image`) kernels into guest memory.
- Added traits and structs for writing boot parameters to guest memory.
