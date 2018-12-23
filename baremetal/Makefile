SOURCES=$(wildcard *.nothing)
IMAGES=$(subst .nothing,.img,$(SOURCES))

all: $(IMAGES)

raspbootin/raspbootcom/raspbootcom:
	git submodule update --init
	$(MAKE) -C raspbootin/raspbootcom

boot: all raspbootin/raspbootcom/raspbootcom
	raspbootin/raspbootcom/raspbootcom /dev/ttyUSB0 raspberrypi.img

clean:
	rm -f *.img *.log

%.img: %.nothing %.startaddr
	pi-nothing-arm-baremetal --start $$(cat $*.startaddr) $* 2>&1 | tee $*.log
