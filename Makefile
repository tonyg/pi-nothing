ifeq ($(shell uname -s),Darwin)
SHARED=-dynamiclib
else
SHARED=-fPIC -shared
endif

KERNEL=kernel

UDIS=udis86-1.7.2

EXAMPLES=\
	hello-x86_64.macho hello-x86_64.elf \
	mandelbrot.macho mandelbrot.elf \
	consing.macho consing.elf

all: disassemblers compiled $(KERNEL).img

raspbootin/raspbootcom/raspbootcom:
	git submodule update --init
	$(MAKE) -C raspbootin/raspbootcom

boot: all raspbootin/raspbootcom/raspbootcom
	raspbootin/raspbootcom/raspbootcom /dev/ttyUSB0 kernel.img

disassemblers: udcli disarm/disarm-0.11

udcli: $(UDIS).tar.gz
	tar -zxvf $<
	(cd $(UDIS); patch -p1 < ../udis-octal.patch)
	(cd $(UDIS); ./configure --disable-shared --prefix=`pwd`/dist && make && make install)
	cp $(UDIS)/dist/bin/udcli .
	rm -rf $(UDIS)

disarm/disarm-0.11:
	make -C disarm

clean: clean-disassemblers clean-racket clean-kernel

clean-disassemblers:
	rm -rf $(UDIS)
	rm -f udcli

clean-racket:
	rm -rf compiled/

clean-kernel:
	rm -f $(KERNEL).img $(KERNEL).log

%.img: %.nothing %.startaddr *.rkt
	racket main-arm.rkt --start $$(cat $*.startaddr) $* 2>&1 | tee $*.log

compiled: *.rkt
	raco make main-arm.rkt exec-macho.rkt exec-elf.rkt

examples: $(EXAMPLES)

clean-examples:
	rm -f $(EXAMPLES)

%.macho: %.nothing
	racket exec-macho.rkt $*
	mv $* $@

%.arm7.elf: %.nothing
	racket exec-elf.rkt -a arm7 $* 2>&1 | tee $*.arm7.log
%.i386.elf: %.nothing
	racket exec-elf.rkt -a i386 $* 2>&1 | tee $*.i386.log
%.x86_64.elf: %.nothing
	racket exec-elf.rkt -a x86_64 $* 2>&1 | tee $*.x86_64.log
