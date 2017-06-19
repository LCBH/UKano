# This Makefile only combines the UKano's and Proverif's Makefile 

#### BUILD#####

PROVERIF =proverif1.92
UKANO =./ukano
UKANO_S =src

all: ukano proverif
ukano:
	@echo "#### Building UKano v0.2 ...."
	$(MAKE) all -C $(UKANO_S)
	cp $(UKANO_S)/ukano .
ukano-short:
	@echo "#### Building UKano v0.2 ...."
	$(MAKE) short -C $(UKANO_S)
	cp $(UKANO_S)/ukano .
proverif:
	@echo "#### Building ProVerif v1.92 ...."
	cd $(PROVERIF) && ./build && cd ..
	cp $(PROVERIF)/proverif .


#### CLEAN ####

GEN_FILES=$(shell find -type f -name '*FOpa.pi' -o  -name '*WAuth.pi')
clean: clean-ukano clean-proverif
clean-ukano:
	@echo "#### Cleaning UKano ...."
	$(MAKE) clean -C $(UKANO_S)
clean-proverif:
	@echo "#### Cleaning ProVerif ...."
	$(MAKE) clean -C $(PROVERIF)
clean-all: clean force
	rm $(GEN_FILES)


#### TEST ####

TESTS=$(shell find examples/tests -type f  -name '*_ok.pi' ! -name '*FOpa.pi' !  -name '*WAuth.pi')
TESTS_ERROR=$(shell find examples/tests -type f  -name '*_error.pi' ! -name '*FOpa.pi' !  -name '*WAuth.pi')
OBJS =$(TESTS:.pi=.ok)
OBJS_ERROR =$(TESTS_ERROR:.pi=.error)

test: $(OBJS_ERROR) $(OBJS)

examples/tests/%.error: examples/tests/%.pi
	@echo "============= UKANO RUN ============="
	@echo "Should return an error !"
	@echo "$$./ukano --less-verbose $<"
# we check that ukano returns an error:
	@$(UKANO) --less-verbose $< ; test $$? -eq 2

examples/tests/%.ok: examples/tests/%.pi
	@echo "============= UKANO RUN ============="
	@echo "Should not return any error !"
	@echo "$$./ukano --less-verbose $<"
	@$(UKANO) --less-verbose $<

force:

.PHONY: clean proverif ukano
