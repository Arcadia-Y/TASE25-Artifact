CURRENT_DIR=.
SETS_DIR = ../sets
FIXPOINT_DIR = ../fixedpoints
MONADLIB_DIR = ../monadlib

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

FLAG = -R $(SETS_DIR) SetsClass -R $(FIXPOINT_DIR) FP -R $(MONADLIB_DIR)/set_monad SetMonad -R $(MONADLIB_DIR)/state_rel_monad StateRelMonad -R $(MONADLIB_DIR)/monad_err MonadErr -R . Examples

FILES = DFS.v ListLib.v KMP.v KMPErr.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(FLAG) > _CoqProject

depend: $(FILES)
	$(COQDEP) $(FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(FLAG) $(FILES) > .depend

clean:
	@rm *.vo *.glob *.vos *.vok .*.aux

.DEFAULT_GOAL := all

-include .depend

