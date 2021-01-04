SRC_DIRS := 'theories' 'ext'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
VFILES := $(shell find 'theories' -name "*.v")

# note this needs to be = since _CoqProject might not exist (if this is a clean
# build)
COQPROJECT_ARGS = $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)
COQ_ARGS := -noglob

# user configurable
Q:=@
TIMED:=false
TIMING_DB:=.timing.sqlite3

COQC := coqc

default: all

all: $(VFILES:.v=.vo)
vos: $(VFILES:.v=.vos)
vok: $(VFILES:.v=.vok)

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning or just building _CoqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject
	@echo "COQC -vok $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(TIMING_ARGS) -vok $(COQ_ARGS) $< -o $@

.PHONY: skip-qed ci

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	rm -f .coqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
