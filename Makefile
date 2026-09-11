# Everyday entrypoints for the ArmoniK.Spec TLA+ project.
#
# Run `make install` once after cloning. Re-run `make update` to refresh tool
# versions (after bumping the pins in scripts/install-tools.sh). Verify a
# single module with the sany / tlc / tlapm targets, or use the exposed
# variables (TLA_CP, TLA_LIB, TLAPM, JAVA_OPTS, TLAPM_OPTS) for ad-hoc
# invocations from the shell.
#
# The largest proof modules do not fit in one upstream tlapm run inside a CI
# job; the optimized prover build checks them whole (make tlapm-opt).

SHELL := /usr/bin/env bash

TOOLS_DIR  := .tlatools
SWITCH_DIR := $(TOOLS_DIR)/opam-switch
SPECS_DIR  := specs

TLA2TOOLS_JAR        := $(TOOLS_DIR)/tla2tools.jar
COMMUNITY_MODULES_JAR := $(TOOLS_DIR)/CommunityModules-deps.jar
COMMUNITY_MODULES_SRC := $(TOOLS_DIR)/CommunityModules/modules

VENV         := .venv
PYTHON       := $(VENV)/bin/python
PY_STAMP     := $(VENV)/.stamp
PY_DEV_STAMP := $(VENV)/.dev-stamp

# Absolute paths, so the variables work from any working directory -- the
# sany and tlc targets run from $(SPECS_DIR), as CI does. TLA_LIB carries the
# module search path the TLAPS-importing modules need (tlapm's stdlib is not
# on the classpath); without it SANY and TLC cannot resolve EXTENDS TLAPS.
JAVA_OPTS  ?= -XX:+UseParallelGC
TLA_CP     := $(CURDIR)/$(TLA2TOOLS_JAR):$(CURDIR)/$(COMMUNITY_MODULES_JAR):$(CURDIR)/$(SPECS_DIR)
TLA_LIB    := -DTLA-Library=$(CURDIR)/$(COMMUNITY_MODULES_SRC):$(CURDIR)/$(TOOLS_DIR)/tlapm/lib/tlapm/stdlib
TLAPM      := $(TOOLS_DIR)/tlapm/bin/tlapm
TLAPM_OPT  := $(TOOLS_DIR)/tlapm-opt/bin/tlapm
# --strict, as CI runs it: omitted and unproved obligations are errors locally too.
TLAPM_OPTS := --strict -I $(CURDIR)/$(COMMUNITY_MODULES_SRC)
# The optimized build reaches the Isabelle-bound obligations of the liveness
# proofs far more concurrently, so they must share the machine instead of having
# it to themselves; --stretch buys back the time that costs them. Measured on
# GraphProcessing2: two obligations Isabelle discharges in 27 s of its 60 s alone
# are lost at --stretch 2 under that concurrency, and the module is green at 3.
TLAPM_OPT_OPTS := $(TLAPM_OPTS) --stretch 3

JAVA_SRCS    := $(wildcard $(SPECS_DIR)/*.java)
JAVA_CLASSES := $(JAVA_SRCS:.java=.class)

# The strict type gate covers the checkers themselves; the tests are verified
# by running them.
MYPY_SRCS := $(filter-out $(wildcard scripts/test_*.py),$(wildcard scripts/*.py))

# Commits to check against the convention of .docs/conventions.md.
RANGE ?= origin/main..HEAD

# Module the sany / tlc / tlapm targets verify, e.g. `make tlc MODULE=GraphProcessing1_mc`.
MODULE ?=

.PHONY: help install install-tlapm-opt update check check-commits python-env build-java test \
        sany tlc tlapm tlapm-opt clean clean-tools

help:
	@echo "targets:"
	@echo "  install        Install the TLA+ toolchain into $(TOOLS_DIR)/ and the Python env into $(VENV)/"
	@echo "  install-tlapm-opt  Install only the optimized tlapm build (826 MB download)"
	@echo "  update         Refresh the toolchain (idempotent; respects pinned versions)"
	@echo "  check          Verify the toolchain install is healthy (no downloads)"
	@echo "  check-commits  Check RANGE=$(RANGE) against the commit convention"
	@echo "  test           Lint (ruff), type-check (mypy --strict) and test the scripts/ checkers"
	@echo "  python-env     Create $(VENV)/ with the dependencies of the scripts/ checks"
	@echo "  build-java     Compile $(SPECS_DIR)/*.java overrides next to the .tla files"
	@echo "  sany MODULE=<mod>    Parse $(SPECS_DIR)/<mod>.tla with SANY"
	@echo "  tlc MODULE=<mod>     Model-check <mod> (log: $(SPECS_DIR)/<mod>.tlc.out)"
	@echo "  tlapm MODULE=<mod>   Check the proofs of $(SPECS_DIR)/<mod>.tla (--strict)"
	@echo "  tlapm-opt MODULE=<mod>  Same, with the optimized tlapm build"
	@echo "  clean          Remove TLC scratch state and compiled .class files"
	@echo "  clean-tools    Remove $(TOOLS_DIR)/ and $(VENV)/ entirely"
	@echo
	@echo "ad-hoc usage:"
	@echo "  \$$(PYTHON) -m scripts.check_property_coverage $(SPECS_DIR)/<mod>.tla"
	@echo "  \$$(PYTHON) -m scripts.check_thm_interface $(SPECS_DIR)/<mod>Theorems.tla"
	@echo "  \$$(PYTHON) -m scripts.check_state_space $(SPECS_DIR)/<mod>.cfg $(SPECS_DIR)/<mod>.tlc.out"
	@echo "  make check-commits RANGE=<base>..<head>"

install: python-env
	./scripts/install-tools.sh

# Separately installable: it is a large download, and CI caches it apart from
# the rest of the toolchain.
install-tlapm-opt:
	@test -n "$(MODULE)" || { echo "usage: make tlapm-opt MODULE=<module>" >&2; exit 2; }
	$(TLAPM_OPT) $(TLAPM_OPT_OPTS) $(SPECS_DIR)/$(MODULE).tla

$(SPECS_DIR)/%.class: $(SPECS_DIR)/%.java $(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR)
	javac -cp $(TLA2TOOLS_JAR):$(COMMUNITY_MODULES_JAR) -d $(SPECS_DIR) $<

clean:
	rm -f $(SPECS_DIR)/*.class $(SPECS_DIR)/*.out
	rm -rf $(SPECS_DIR)/states __tlacache__ .tlacache

clean-tools:
	rm -rf $(TOOLS_DIR) $(VENV)
