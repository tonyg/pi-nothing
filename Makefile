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
	$(CC) -o $@ -shared -I beaengine/dist/include -Lbeaengine/dist $< -lBeaEngine_s_d

%: %.c beaengine/dist
	$(CC) -o $@ -I beaengine/dist/include -Lbeaengine/dist $< -lBeaEngine_s_d

clean:
	rm -rf beaengine
	rm -f beaengine-wrapper.so
