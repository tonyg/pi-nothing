SOURCES=$(wildcard *.nothing)
I386_ELF_TARGETS=$(subst .nothing,.i386.elf,$(SOURCES))
X86_64_ELF_TARGETS=$(subst .nothing,.x86_64.elf,$(SOURCES))
ARM7_ELF_TARGETS=$(subst .nothing,.arm7.elf,$(SOURCES))

all: $(I386_ELF_TARGETS) $(X86_64_ELF_TARGETS) $(ARM7_ELF_TARGETS)

%.arm7.elf: %.nothing
	pi-nothing-elf -a arm7 $* 2>&1 | tee $*.arm7.log
%.i386.elf: %.nothing
	pi-nothing-elf -a i386 $* 2>&1 | tee $*.i386.log
%.x86_64.elf: %.nothing
	pi-nothing-elf -a x86_64 $* 2>&1 | tee $*.x86_64.log

clean:
	rm -f $(I386_ELF_TARGETS) $(X86_64_ELF_TARGETS) $(ARM7_ELF_TARGETS)
	rm -f *.log
