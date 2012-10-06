ifeq ($(shell uname -s),Darwin)
SHARED=-dynamiclib
else
SHARED=-shared
endif

KERNEL=kernel

all: disassemblers compiled/main-arm_rkt.zo $(KERNEL).img

disassemblers: beaengine-wrapper.so disarm/disarm-0.11

beaengine: beaengine-sources.zip
	mkdir $@
	(cd $@; unzip ../$<)

beaengine/dist: beaengine
	mkdir $@
	(cd beaengine; cmake sources)
	(cd beaengine; make)
	cp beaengine/sources/lib/*/*.a $@
	cp -r beaengine/sources/include $@

disarm/disarm-0.11:
	make -C disarm

%.so: %.c beaengine/dist
	$(CC) -o $@ $(SHARED) -I beaengine/dist/include -Lbeaengine/dist $< -lBeaEngine_s_d

%: %.c beaengine/dist
	$(CC) -o $@ -I beaengine/dist/include -Lbeaengine/dist $< -lBeaEngine_s_d

clean: clean-disassemblers clean-racket clean-kernel

clean-disassemblers:
	rm -rf beaengine
	rm -f beaengine-wrapper.so

clean-racket:
	rm -rf compiled/

clean-kernel:
	rm -f $(KERNEL).img $(KERNEL).log

%.img: %.nothing %.startaddr *.rkt
	racket main-arm.rkt --start $$(cat $*.startaddr) $* 2>&1 | tee $*.log

compiled/main-arm_rkt.zo: *.rkt
	raco make main-arm.rkt
