default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -Q . "StructTact" *.v > Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

.PHONY: Makefile.coq default clean
