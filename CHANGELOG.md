# [v0.4.0]

## Fixed

- [[#66]](https://github.com/rust-vmm/linux-loader/issues/66) Fixed potential
  overflow in calls to `align_up`.

## Changed

- [[#62]](https://github.com/rust-vmm/linux-loader/issues/62) The
  `load_cmdline` function now takes as a parameter the crate defined
  `Cmdline` object instead of `Cstr`. This means that customers don't need to
  convert the object before calling into `load_cmdline`.
- [[#83]](https://github.com/rust-vmm/linux-loader/issues/83) Updated the
  vm-memory dependency requirement to the latest version (0.6.0).

## Added

- [[#79]](https://github.com/rust-vmm/linux-loader/pull/79) Implemented
  `From<Cmdline>` for `Vec<u8>`. This replaces the obsolete `Into`
  implementation.

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
