CURRENT_DIR=.

-include CONFIGURE

echo_dir : 
	@echo "COQBIN=$(COQBIN)" > SUB_CONFIGURE
	@echo "SUF=$(SUF)" >> SUB_CONFIGURE

SET_MAKE : 
	cp SUB_CONFIGURE $(CURRENT_DIR)/sets/CONFIGURE
	cd sets && $(MAKE) depend && $(MAKE) all -j5

FIX_MAKE : 
	cp SUB_CONFIGURE $(CURRENT_DIR)/fixedpoints/CONFIGURE
	cd fixedpoints && $(MAKE) depend && $(MAKE) all -j5

MONAD_MAKE : 
	cp SUB_CONFIGURE $(CURRENT_DIR)/monadlib/CONFIGURE
	cd monadlib && $(MAKE) depend && $(MAKE) all -j5

all : echo_dir SET_MAKE FIX_MAKE MONAD_MAKE
	@echo "All subdirectories have been built."

clean:
	cd sets && $(MAKE) clean
	cd fixedpoints && $(MAKE) clean
	cd monadlib && $(MAKE) clean

.PHONY: clean depend
.DEFAULT_GOAL := all

-include .depend

-include $(DEPS)
