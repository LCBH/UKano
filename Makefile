# This Makefile only combines the UKano's and Proverif's Makefile 

#### BUILD#####

PROVERIF =proverif1.96/src
UKANO =./ukano
UKANO_S =src

all: ukano
ukano:
	@echo "#### Building UKano ...."
	$(MAKE) all -C $(UKANO_S)
	cp $(UKANO_S)/ukano .
ukano-short:
	@echo "#### Building UKano ...."
	$(MAKE) short -C $(UKANO_S)
	cp $(UKANO_S)/ukano .
proverif:
	@echo "#### Building ProVerif ...."
	$(MAKE) all -C $(PROVERIF)
	cp $(PROVERIF)/proverif .


#### CLEAN ####

GEN_FILES=$(shell find -type f -name '*FOpa.pi' -o  -name '*WAuth.pi')
clean: clean-ukano
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
	-@rm $@

examples/tests/%.ok: examples/tests/%.pi
	@echo "============= UKANO RUN ============="
	@echo "Should not return any error !"
	@echo "$$./ukano --less-verbose $<"
	@$(UKANO) --less-verbose $<
	-@rm $@

force:

.PHONY: clean proverif ukano
