# Linux-loader

## Short-description

* Parsing and loading vmlinux (raw ELF image) and bzImage images
* Linux command line parsing and generation
* Definitions and helpers for the Linux boot protocol

## How to build

```
cd linux-loader
cargo build
```

## How to run test for Elf loader

```shell
# Assuming your linux-loader is under $HOME
$ cd linux-loader
$ cargo test
$ cargo test -- --nocapture
```

## How to run test for bzImage loader

As we don't want to distribute an entire kernel bzImage, the `load_bzImage` test is ignored by
default. In order to test the bzImage support, one needs to locally build a bzImage, copy it
to the `src/loader` directory and run the ignored test:

```shell
# Assuming your linux-loader and linux-stable are both under $LINUX_LOADER
$ git clone git://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git $LINUX_LOADER/linux-stable
$ cd linux-stable
$ make bzImage 
$ cp linux-stable/arch/x86/boot/bzImage $LINUX_LOADER/linux-loader/src/loader/
$ cd $LINUX_LOADER/linux-loader
$ cargo test -- --ignored
```

## Platform Support
- Arch: x86
- OS: Linux/Unix

