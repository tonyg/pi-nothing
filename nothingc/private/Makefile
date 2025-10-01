UDIS=udis86-1.7.2

all: disassemblers

disassemblers: udcli disarm/disarm-0.11

udcli: $(UDIS).tar.gz
	tar -zxvf $<
	(cd $(UDIS); patch -p1 < ../udis-octal.patch)
	(cd $(UDIS); ./configure --disable-shared --with-python=python3 --prefix=`pwd`/dist && make && make install)
	cp $(UDIS)/dist/bin/udcli .
	rm -rf $(UDIS)

disarm/disarm-0.11:
	make -C disarm

clean: clean-disassemblers clean-elf-hash

clean-disassemblers:
	rm -rf $(UDIS)
	rm -f udcli
	rm -f disarm/disarm-0.11

test-elf-hash: elf-hash
	./elf-hash 100000 | racket ../elf-hash.rkt
	rm -f elf-hash

elf-hash: elf-hash.c
	gcc -O3 -o $@ $<

clean-elf-hash:
	rm -f elf-hash
