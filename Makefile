# Everyday entrypoints for the ArmoniK.Spec TLA+ project.
#
# Run `make install` once after cloning. Re-run `make update` to refresh tool
# versions (after bumping the pins in scripts/install-tools.sh). Use the
# exposed variables (TLA_CP, TLAPM, JAVA_OPTS, TLAPM_OPTS) for ad-hoc TLC
# or tlapm invocations from the shell.

SHELL := /usr/bin/env bash

TOOLS_DIR  := .tlatools
SWITCH_DIR := $(TOOLS_DIR)/opam-switch
SPECS_DIR  := specs

TLA2TOOLS_JAR        := $(TOOLS_DIR)/tla2tools.jar
COMMUNITY_MODULES_JAR := $(TOOLS_DIR)/CommunityModules-deps.jar
COMMUNITY_MODULES_SRC := $(TOOLS_DIR)/CommunityModules/modules

VENV     := .venv
PYTHON   := $(VENV)/bin/python
PY_STAMP := $(VENV)/.stamp

JAVA_OPTS  ?= -XX:+UseParallelGC
TLA_CP     := $(TLA2TOOLS_JAR):$(COMMUNITY_MODULES_JAR):$(SPECS_DIR)
TLAPM      := $(TOOLS_DIR)/tlapm/bin/tlapm
TLAPM_OPTS := -I $(COMMUNITY_MODULES_SRC)

JAVA_SRCS    := $(wildcard $(SPECS_DIR)/*.java)
JAVA_CLASSES := $(JAVA_SRCS:.java=.class)

.PHONY: help install update check python-env build-java clean clean-tools

help:
	@echo "targets:"
	@echo "  install      Install the TLA+ toolchain into $(TOOLS_DIR)/ and the Python env into $(VENV)/"
	@echo "  update       Refresh the toolchain (idempotent; respects pinned versions)"
	@echo "  check        Verify the toolchain install is healthy (no downloads)"
	@echo "  python-env   Create $(VENV)/ with the dependencies of the scripts/ checks"
	@echo "  build-java   Compile $(SPECS_DIR)/*.java overrides next to the .tla files"
	@echo "  clean        Remove TLC scratch state and compiled .class files"
	@echo "  clean-tools  Remove $(TOOLS_DIR)/ and $(VENV)/ entirely"
	@echo
	@echo "ad-hoc usage:"
	@echo "  java \$$(JAVA_OPTS) -cp \$$(TLA_CP) tlc2.TLC -config $(SPECS_DIR)/<mod>.cfg <mod>"
	@echo "  \$$(TLAPM) \$$(TLAPM_OPTS) $(SPECS_DIR)/<mod>Theorems_proofs.tla"
	@echo "  \$$(PYTHON) -m scripts.check_property_coverage $(SPECS_DIR)/<mod>.tla"
	@echo "  \$$(PYTHON) -m scripts.check_thm_interface $(SPECS_DIR)/<mod>Theorems.tla"

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

$(TOOLS_DIR)/tla2tools.jar $(TOOLS_DIR)/CommunityModules-deps.jar:
	$(MAKE) install

build-java: $(JAVA_CLASSES)

$(SPECS_DIR)/%.class: $(SPECS_DIR)/%.java $(TLA2TOOLS_JAR) $(COMMUNITY_MODULES_JAR)
	javac -cp $(TLA2TOOLS_JAR):$(COMMUNITY_MODULES_JAR) -d $(SPECS_DIR) $<

clean:
	rm -f $(SPECS_DIR)/*.class $(SPECS_DIR)/*.out
	rm -rf $(SPECS_DIR)/states __tlacache__ .tlacache

clean-tools:
	rm -rf $(TOOLS_DIR) $(VENV)
