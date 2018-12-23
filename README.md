# Programming language, compiler, and operating system for bare-metal ARM

## Quickstart

To run the main
[baremetal Raspberry Pi kernel](baremetal/raspberrypi.nothing),

    $ git clone git://github.com/tonyg/pi-nothing.git
    $ make link all
    $ cp baremetal/raspberrypi.img /PATH/TO/YOUR/RASPBERRY/PI/SDCARD/kernel.img

Boot the Raspberry Pi.

There is also a [simpler kernel](baremetal/versatilepb.nothing) for
the QEMU-emulated
[`versatilepb`](https://wiki.qemu.org/Documentation/Platforms/ARM)
machine that can be run in emulation from the host:

    $ cd baremetal
    $ make versatilepb.img
    $ ./run-kernel

A [graphical variant](baremetal/versatilepb-graphics.nothing) also
exists.

When running a `versatilepb` kernel in emulation, you're interacting
with the kernel via the emulated board's serial UART. Type characters
at it, and it will echo them. When you get bored of this, press `C-a
x` to quit `qemu`.

## Third-party software

This package makes use of a number of programs and resources
generously developed and released as free software by other authors:

 - [**disarm**](nothingc/private/disarm), a disassembler for ARM
   instructions, developed by and copyright to Gareth McCaughan.

 - [**udis**](nothingc/private/udis86-1.7.2.tar.gz), a disassembler
   for x86 and x86-64, written by and copyright to Vivek Thampi.

 - [**font0**](baremetal/font0.bin), a very simple monospace bitmapped
   font developed by and copyright to Bitstream, Inc.

 - [**raspbootin**](baremetal/raspbootin), a boot-over-serial
   bootloader for the Raspberry Pi, developed by and copyright to
   Goswin von Brederlow.

and, of course, [QEMU](https://www.qemu.org/) and
[Racket](https://racket-lang.org/) themselves.
