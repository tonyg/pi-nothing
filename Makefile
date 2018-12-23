PACKAGENAME=nothingc
COLLECTS=nothingc

all: setup
	$(MAKE) -C baremetal

clean:
	$(MAKE) -C nothingc/private clean
	$(MAKE) -C baremetal clean
	find . -name compiled -type d | xargs rm -rf

setup:
	raco setup $(COLLECTS)

link:
	raco pkg install --link -n $(PACKAGENAME) $$(pwd)/nothingc

unlink:
	raco pkg remove $(PACKAGENAME)
