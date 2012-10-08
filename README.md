# Programming language, compiler, and operating system for bare-metal ARM

## Quickstart

    $ git clone git://github.com/tonyg/pi-nothing.git
    $ make
    $ cp kernel.img /PATH/TO/YOUR/RASPBERRY/PI/SDCARD

Boot the Raspberry Pi.

Alternatively,

    $ make versatilepb.img
    $ ./run-kernel

## Details

This command compiles the ARM disassembler `disarm`, copyright Gareth
McCaughan:

    $ make -C disarm

This command compiles the kernel source from `kernel.nothing` into
`kernel.img`:

    $ racket main-arm.rkt --start $(cat kernel.startaddr) kernel

## Using qemu-system-arm instead of the Raspberry Pi

This command compiles `versatilepb.nothing` into `versatilepb.img`:

    $ racket main-arm.rkt --start $(cat versatilepb.startaddr) versatilepb

This command fires up `qemu-system-arm` with `versatilepb.img`:

    $ ./run-kernel 

The graphical output is disabled at present. You're interacting with
the kernel via the emulated board's serial UART. Type characters at
it, and it will echo them. When you get bored of this, press `C-a x`
to quit `qemu`.

Note that `versatilepb.nothing` *polls* the UART for input at present,
so `qemu` will take 100% of your CPU while it's running!
