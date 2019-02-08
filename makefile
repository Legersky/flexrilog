# This Makefile is for convenience as a reminder and shortcut for the most used commands

# Package folder
PACKAGE = rigid_and_flexible_graphs

# change to your sage command if needed
SAGE = sage

all: install test

install:
	$(SAGE) -pip install --upgrade --no-index -v .

uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

develop:
	$(SAGE) -pip install --upgrade -e .

test:
	$(SAGE) setup.py test

test-parallel:
	$(SAGE) -t --force-lib -i -p 4 $(PACKAGE)

test-long:
	$(SAGE) -t --long --force-lib -i -p 4 $(PACKAGE)

test-all:
	$(SAGE) -t --long --force-lib --optional=all -i -p 4 $(PACKAGE)

coverage:
	$(SAGE) -coverage $(PACKAGE)/*

doc:
	cd doc && $(SAGE) -sh -c "make html"

doc-pdf:
	cd doc && $(SAGE) -sh -c "make latexpdf"

clean: clean-doc

clean-doc:
	cd doc && $(SAGE) -sh -c "make clean"

.PHONY: all install develop test test-parallel test-long test-all coverage clean clean-doc doc doc-pdf
