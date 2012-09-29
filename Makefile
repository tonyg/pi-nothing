ifeq ($(shell uname -s),Darwin)
SHARED=-dynamiclib
else
SHARED=-shared
endif

all: beaengine-wrapper.so

beaengine: beaengine-sources.zip
	mkdir $@
	(cd $@; unzip ../$<)

beaengine/dist: beaengine
	mkdir $@
	(cd beaengine; cmake sources)
	(cd beaengine; make)
	cp beaengine/sources/lib/*/*.a $@
	cp -r beaengine/sources/include $@

%.so: %.c beaengine/dist
	$(CC) -o $@ $(SHARED) -I beaengine/dist/include -Lbeaengine/dist $< -lBeaEngine_s_d

%: %.c beaengine/dist
	$(CC) -o $@ -I beaengine/dist/include -Lbeaengine/dist $< -lBeaEngine_s_d

clean:
	rm -rf beaengine
	rm -f beaengine-wrapper.so

###########################################################################

kernel.bin: kernel.nothing *.rkt
	racket main-arm.rkt
