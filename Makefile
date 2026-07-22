SHELL := /bin/bash

.PHONY: doc doc-compcert

doc:
	bash tools/gen_coqdoc.sh

doc-compcert:
	$(MAKE) -C coq-compcert.3.17 documentation
