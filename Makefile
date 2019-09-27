MF_COQ := Makefile.coq

all: $(MF_COQ)
	$(MAKE) -f $< $@

install: $(MF_COQ) all
	$(MAKE) -f $< $@

uninstall: $(MF_COQ)
	$(MAKE) -f $< $@

$(MF_COQ): _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

clean:
	if [ -e $(MF_COQ) ]; then $(MAKE) -f $(MF_COQ) cleanall; fi
	$(RM) $(MF_COQ)* .coqdeps.d
