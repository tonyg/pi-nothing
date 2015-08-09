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

raspbootin:
	git submodule update --init

raspbootin/raspbootcom/raspbootcom: raspbootin
	$(MAKE) -C raspbootin/raspbootcom

boot: all raspbootin/raspbootcom/raspbootcom
	raspbootin/raspbootcom/raspbootcom /dev/ttyUSB0 kernel.img

disassemblers: udcli disarm/disarm-0.11

udcli: $(UDIS).tar.gz
	tar -zxvf $<
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

%.elf: %.nothing
	racket exec-elf.rkt $*
	mv $* $@
