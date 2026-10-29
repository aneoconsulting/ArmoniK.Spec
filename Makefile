# Everyday entrypoints for the ArmoniK.Spec TLA+ project.
#
# Run `make install` once after cloning, and again after bumping the pinned
# versions in scripts/install-tools.sh. Verify a single module with the sany /
# tlc / tlapm / tlapm-opt targets, which CI runs too, or use the exposed
# variables (TLA_CP, TLA_LIB, TLAPM, TLAPM_OPT, JAVA_OPTS, TLAPM_OPTS,
# TLAPM_OPT_OPTS) for ad-hoc invocations from the shell.
#
# The modules live in three flat directories: specs/ holds the specifications,
# lib/ the library modules they build on, lib/temporal/ the temporal theorems
# (one per interface <X>Theorems.tla, proved in <X>Theorems_proofs.tla). A module
# name is unique across them, so the single-module targets take a bare
# MODULE=<name> and locate it in whichever directory holds it; the three
# directories are on the search path and the classpath every tool gets.
#
# scripts/chunk_proofs.py plans how each proof module is checked (see its
# docstring); `make chunks` prints the plan.

SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c

TOOLS_DIR  := .tlatools
SPECS_DIR  := specs
LIB_DIR    := lib
TEMPORAL_DIR := lib/temporal
MODULE_DIRS := $(SPECS_DIR) $(LIB_DIR) $(TEMPORAL_DIR)

TLA2TOOLS_JAR        := $(TOOLS_DIR)/tla2tools.jar
COMMUNITY_MODULES_JAR := $(TOOLS_DIR)/CommunityModules-deps.jar
COMMUNITY_MODULES_SRC := $(TOOLS_DIR)/CommunityModules/modules

VENV         := .venv
PYTHON       := $(VENV)/bin/python
PY_STAMP     := $(VENV)/.stamp
PY_DEV_STAMP := $(VENV)/.dev-stamp

# Absolute paths, so the variables work from any working directory -- the
# sany and tlc targets run from the module's directory. TLA_LIB
# carries the module search path: the TLAPS-importing modules need tlapm's
# stdlib (not on the classpath; without it SANY and TLC cannot resolve EXTENDS
# TLAPS), a specification needs the libraries of $(LIB_DIR), and its proofs the
# temporal theorems of $(TEMPORAL_DIR) they instantiate. The .class overrides
# of $(LIB_DIR) are reached through the classpath, hence TLA_CP lists the
# module directories too.
JAVA_OPTS  ?= -XX:+UseParallelGC
TLA_CP     := $(CURDIR)/$(TLA2TOOLS_JAR):$(CURDIR)/$(COMMUNITY_MODULES_JAR):$(CURDIR)/$(LIB_DIR):$(CURDIR)/$(TEMPORAL_DIR):$(CURDIR)/$(SPECS_DIR)
TLA_LIB    := -DTLA-Library=$(CURDIR)/$(COMMUNITY_MODULES_SRC):$(CURDIR)/$(TOOLS_DIR)/tlapm/lib/tlapm/stdlib:$(CURDIR)/$(LIB_DIR):$(CURDIR)/$(TEMPORAL_DIR):$(CURDIR)/$(SPECS_DIR)
TLAPM      := $(TOOLS_DIR)/tlapm/bin/tlapm
TLAPM_OPT  := $(TOOLS_DIR)/tlapm-opt/bin/tlapm
# --strict, as CI runs it: omitted and unproved obligations are errors locally too.
TLAPM_OPTS := --strict -I $(CURDIR)/$(COMMUNITY_MODULES_SRC) -I $(CURDIR)/$(LIB_DIR) -I $(CURDIR)/$(TEMPORAL_DIR) -I $(CURDIR)/$(SPECS_DIR)
# The optimized build reaches the Isabelle-bound obligations of the liveness
# proofs far more concurrently, so they must share the machine instead of having
# it to themselves; --stretch buys back the time that costs them. Measured on
# Graph2: two obligations Isabelle discharges in 27 s of its 60 s alone
# are lost at --stretch 2 under that concurrency, and the module is green at 3.
TLAPM_OPT_OPTS := $(TLAPM_OPTS) --stretch 3
# Options of scripts/chunk_proofs.py for the chunks target, e.g.
# CHUNK_OPTS="--budget 800 --max-steps 30". Empty means the script's defaults,
# which it owns.
CHUNK_OPTS ?=
# Optional line range for the tlapm / tlapm-opt targets: empty checks the whole
# module, BEGIN/END restrict the run to that range (see `make chunks`).
TOOLBOX     = $(if $(BEGIN),$(if $(END),--toolbox $(BEGIN) $(END),$(error BEGIN needs a matching END)))

JAVA_SRCS    := $(wildcard $(LIB_DIR)/*.java)
JAVA_CLASSES := $(JAVA_SRCS:.java=.class)

# The strict type gate covers the checkers themselves; the tests are verified
# by running them.
MYPY_SRCS := $(filter-out $(wildcard scripts/test_*.py),$(wildcard scripts/*.py))

# Commits to check against the convention of .docs/conventions.md.
RANGE ?= origin/main..HEAD

# Module the sany / tlc / tlapm targets verify, e.g. `make tlc MODULE=Graph1_mc`
# or `make tlapm MODULE=DDGraphTheorems_proofs`: a bare name, located below.
MODULE ?=
# The directory of $(MODULE_DIRS) holding $(MODULE).tla; empty when none does.
# Recursively expanded, so it follows MODULE.
MODULE_DIR = $(firstword $(foreach d,$(MODULE_DIRS),$(if $(wildcard $(d)/$(MODULE).tla),$(d))))
# Guard of the single-module targets: MODULE is given and names a module of one
# of the module directories. $(1) is the rest of the usage line.
locate = test -n "$(MODULE)" || { echo "usage: make $@ MODULE=<module>$(1)" >&2; exit 2; }; \
         test -n "$(MODULE_DIR)" || { echo "$(MODULE).tla: no such module in $(MODULE_DIRS)" >&2; exit 2; }

.PHONY: help install install-tlapm-opt check check-commits python-env build-java test \
        sany tlc tlapm tlapm-opt chunks clean clean-tools

help:
	@echo "targets:"
	@echo "  install        Install the TLA+ toolchain into $(TOOLS_DIR)/ and the Python env into $(VENV)/"
	@echo "  install-tlapm-opt  Install only the optimized tlapm build (826 MB download)"
	@echo "  check          Verify the toolchain install is healthy (no downloads)"
	@echo "  check-commits  Check RANGE=$(RANGE) against the commit convention"
	@echo "  test           Lint (ruff), type-check (mypy --strict) and test the scripts/ checkers"
	@echo "  python-env     Create $(VENV)/ with the dependencies of the scripts/ checks"
	@echo "  build-java     Compile the $(LIB_DIR)/*.java overrides next to the .tla files"
	@echo "  sany MODULE=<mod>    Parse <mod>.tla with SANY"
	@echo "  tlc MODULE=<mod>     Model-check <mod> (log: <dir>/<mod>.tlc.out)"
	@echo "  tlapm MODULE=<mod>   Check the proofs of <mod>.tla (--strict)"
	@echo "                       add BEGIN=<line> END=<line> to check one range only"
	@echo "  tlapm-opt MODULE=<mod>     Same, with the optimized tlapm build"
	@echo "  chunks [MODULE=<mod>]      Print the ranges of <mod> (default: every proof module)"
	@echo "  clean          Remove TLC scratch state, *.out logs and compiled .class files"
	@echo "  clean-tools    Remove $(TOOLS_DIR)/ and $(VENV)/ entirely"
	@echo
	@echo "<mod> is a bare module name, found in $(SPECS_DIR)/ (specifications), $(LIB_DIR)/ (libraries)"
	@echo "or $(TEMPORAL_DIR)/ (temporal theorems)."
	@echo
	@echo "ad-hoc usage:"
	@echo "  \$$(PYTHON) -m scripts.check_property_coverage $(SPECS_DIR)/<mod>.tla"
	@echo "  \$$(PYTHON) -m scripts.check_thm_interface <dir>/<mod>Theorems.tla"
	@echo "  \$$(PYTHON) -m scripts.check_state_space <dir>/<mod>.cfg <dir>/<mod>.tlc.out"
	@echo "  make check-commits RANGE=<base>..<head>"

install: python-env
	./scripts/install-tools.sh

# Separately installable: it is a large download, and CI caches it apart from
# the rest of the toolchain.
install-tlapm-opt:
	./scripts/install-tools.sh --only-tlapm-opt

# The venv is rebuilt from scratch whenever the pinned requirements change.
python-env: $(PY_STAMP)

$(PY_STAMP): scripts/requirements.txt
	rm -rf $(VENV)
	python3 -m venv $(VENV)
	$(VENV)/bin/pip install --quiet --requirement scripts/requirements.txt
	touch $@

check:
	./scripts/install-tools.sh --check

# Standard library only, so it runs without `make install`.
check-commits:
	python3 -m scripts.check_commit --range $(RANGE)

# The dev dependencies (pytest) ride on top of the pinned runtime venv.
$(PY_DEV_STAMP): scripts/requirements-dev.txt $(PY_STAMP)
	$(VENV)/bin/pip install --quiet --requirement scripts/requirements-dev.txt
	touch $@

test: $(PY_DEV_STAMP)
	$(VENV)/bin/ruff check scripts
	$(PYTHON) -m mypy --strict $(MYPY_SRCS)
	$(PYTHON) -m pytest scripts

# The toolchain is a large download: `make install` alone fetches it, never a
# verification target as a side effect.
$(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR) $(TLAPM) $(TLAPM_OPT):
	@echo "$@ is missing: run make install" >&2; exit 1

build-java: $(JAVA_CLASSES)

# Single-module verification, as CI runs it.
sany: $(TLA2TOOLS_JAR)
	@$(call locate)
	cd $(MODULE_DIR) && java $(TLA_LIB) -cp $(TLA_CP) tla2sany.SANY -error-codes "$(MODULE).tla"

tlc: $(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR) build-java
	@$(call locate)
	cd $(MODULE_DIR) && \
	java $(JAVA_OPTS) $(TLA_LIB) -cp $(TLA_CP) tlc2.TLC -config "$(MODULE).cfg" "$(MODULE)" \
	| tee "$(MODULE).tlc.out"

tlapm: $(TLAPM)
	@$(call locate, [BEGIN=<line> END=<line>])
	$(TLAPM) $(TLAPM_OPTS) $(TOOLBOX) $(MODULE_DIR)/$(MODULE).tla

tlapm-opt: $(TLAPM_OPT)
	@$(call locate, [BEGIN=<line> END=<line>])
	$(TLAPM_OPT) $(TLAPM_OPT_OPTS) $(TOOLBOX) $(MODULE_DIR)/$(MODULE).tla

chunks:
	@test -z "$(MODULE)" || $(call locate)
	python3 -m scripts.chunk_proofs $(CHUNK_OPTS) $(if $(MODULE),$(MODULE_DIR)/$(MODULE).tla)

# A .class lands next to its .java.
%.class: %.java $(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR)
	javac -cp $(TLA2TOOLS_JAR):$(COMMUNITY_MODULES_JAR) -d $(@D) $<

clean:
	rm -f $(addsuffix /*.class,$(MODULE_DIRS)) $(addsuffix /*.out,$(MODULE_DIRS))
	rm -rf $(addsuffix /states,$(MODULE_DIRS)) __tlacache__ .tlacache

clean-tools:
	rm -rf $(TOOLS_DIR) $(VENV)
