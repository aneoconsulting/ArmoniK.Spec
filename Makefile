# Everyday entrypoints for the ArmoniK.Spec TLA+ project.
#
# Run `make install` once after cloning. Re-run `make update` to refresh tool
# versions (after bumping the pins in scripts/install-tools.sh). Verify a
# single module with the sany / tlc / tlapm targets, or use the exposed
# variables (TLA_CP, TLA_LIB, TLAPM, JAVA_OPTS, TLAPM_OPTS) for ad-hoc
# invocations from the shell.

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
# --strict, as CI runs it: omitted and unproved obligations are errors locally too.
TLAPM_OPTS := --strict -I $(CURDIR)/$(COMMUNITY_MODULES_SRC)

JAVA_SRCS    := $(wildcard $(SPECS_DIR)/*.java)
JAVA_CLASSES := $(JAVA_SRCS:.java=.class)

# Commits to check against the convention of .docs/conventions.md.
RANGE ?= origin/main..HEAD

# Module the sany / tlc / tlapm targets verify, e.g. `make tlc MODULE=GraphProcessing1_mc`.
MODULE ?=

.PHONY: help install update check check-commits python-env build-java test sany tlc tlapm clean clean-tools

help:
	@echo "targets:"
	@echo "  install        Install the TLA+ toolchain into $(TOOLS_DIR)/ and the Python env into $(VENV)/"
	@echo "  update         Refresh the toolchain (idempotent; respects pinned versions)"
	@echo "  check          Verify the toolchain install is healthy (no downloads)"
	@echo "  check-commits  Check RANGE=$(RANGE) against the commit convention"
	@echo "  test           Run the scripts/ test suite (installs pytest into $(VENV)/)"
	@echo "  python-env     Create $(VENV)/ with the dependencies of the scripts/ checks"
	@echo "  build-java     Compile $(SPECS_DIR)/*.java overrides next to the .tla files"
	@echo "  sany MODULE=<mod>    Parse $(SPECS_DIR)/<mod>.tla with SANY"
	@echo "  tlc MODULE=<mod>     Model-check <mod> (log: $(SPECS_DIR)/<mod>.tlc.out)"
	@echo "  tlapm MODULE=<mod>   Check the proofs of $(SPECS_DIR)/<mod>.tla (--strict)"
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

update: install

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
	$(PYTHON) -m pytest scripts

$(TOOLS_DIR)/tla2tools.jar $(TOOLS_DIR)/CommunityModules-deps.jar:
	$(MAKE) install

build-java: $(JAVA_CLASSES)

# Single-module verification, mirroring what CI runs (same flags, same cwd).
sany: $(TLA2TOOLS_JAR)
	@test -n "$(MODULE)" || { echo "usage: make sany MODULE=<module>" >&2; exit 2; }
	cd $(SPECS_DIR) && java $(TLA_LIB) -cp $(TLA_CP) tla2sany.SANY -error-codes "$(MODULE).tla"

tlc: $(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR) build-java
	@test -n "$(MODULE)" || { echo "usage: make tlc MODULE=<module>" >&2; exit 2; }
	cd $(SPECS_DIR) && set -o pipefail && \
	java $(JAVA_OPTS) $(TLA_LIB) -cp $(TLA_CP) tlc2.TLC -config "$(MODULE).cfg" "$(MODULE)" \
	| tee "$(MODULE).tlc.out"

tlapm:
	@test -n "$(MODULE)" || { echo "usage: make tlapm MODULE=<module>" >&2; exit 2; }
	$(TLAPM) $(TLAPM_OPTS) $(SPECS_DIR)/$(MODULE).tla

$(SPECS_DIR)/%.class: $(SPECS_DIR)/%.java $(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR)
	javac -cp $(TLA2TOOLS_JAR):$(COMMUNITY_MODULES_JAR) -d $(SPECS_DIR) $<

clean:
	rm -f $(SPECS_DIR)/*.class $(SPECS_DIR)/*.out
	rm -rf $(SPECS_DIR)/states __tlacache__ .tlacache

clean-tools:
	rm -rf $(TOOLS_DIR) $(VENV)
