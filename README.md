# Programming language, compiler, and operating system for bare-metal ARM

## Quickstart

    $ git clone git@vapour.eighty-twenty.org:4-move.git
    $ cd 4-move/nothingc
    $ make -C disarm
    $ racket main-arm.rkt
    $ ./run-kernel 

## Details

This command compiles the ARM disassembler `disarm`, copyright Gareth
McCaughan:

    $ make -C disarm

This command compiles the kernel source from `kernel.nothing` into
`kernel.bin`:

    $ racket main-arm.rkt

This command fires up `qemu-system-arm` with `kernel.bin`:

    $ ./run-kernel 

The graphical output is disabled at present. You're interacting with
the kernel via the emulated board's serial UART. Type characters at
it, and it will echo them. When you get bored of this, press `C-a x`
to quit `qemu`.

Note that `kernel.nothing` *polls* the UART for input at present, so
`qemu` will take 100% of your CPU while it's running!
