# This Makefile is for convenience as a reminder and shortcut for the most used commands

# Package folder
PACKAGE = flexrilog

# change to your sage command if needed
SAGE = sage

all: install test

install:
	$(SAGE) -pip install --upgrade -v .

install-user:
	$(SAGE) -pip install --upgrade --user -v .
	
uninstall:
	$(SAGE) -pip uninstall $(PACKAGE)

develop:
	$(SAGE) -pip install --upgrade -e .

test:
	$(SAGE) setup.py test

test-long:
	$(SAGE) setup.py testLong

test-all:
	$(SAGE) setup.py testAll

coverage:
	$(SAGE) -coverage $(PACKAGE)/*

doc:
	cd doc && $(SAGE) -sh -c "make html"

doc-pdf:
	cd doc && $(SAGE) -sh -c "make latexpdf"

clean: clean-doc

clean-doc:
	cd doc && $(SAGE) -sh -c "make clean"

.PHONY: all install install-user develop test test-long test-all coverage clean clean-doc doc doc-pdf
