# This Makefile only combines the UKano's and Proverif's Makefile 

PROVERIF =proverif1.96/src
UKANO =src

all: ukano proverif

ukano:
	@echo "## Building UKano ...."
	$(MAKE) all -C $(UKANO)
	cp $(UKANO)/ukano .

proverif:
	@echo "## Building ProVerif ...."
	$(MAKE) all -C $(PROVERIF)
	cp $(PROVERIF)/proverif .

clean:
	@echo "## Cleaning UKano ...."
	$(MAKE) clean -C $(UKANO)
	@echo "## Cleaning ProVerif ...."
	$(MAKE) clean -C $(PROVERIF)

.PHONY: clean proverif ukano
