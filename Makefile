.DEFAULT_GOAL := build

# The two roots share expensive dependencies and Agda's interface cache.
.NOTPARALLEL:
.PHONY: build build-set build-gpd clean help

build: build-set build-gpd

build-set:
	agda examples/Examples.agda

build-gpd:
	agda examples/ExamplesGpd.agda

clean:
	rm -rf _build MAlonzo
	find Bonak examples -type f -name '*.agdai' -delete

help:
	@printf '%s\n' \
	  'make [build]  Check both example roots and their library dependencies' \
	  'make build-set  Check the νSet examples' \
	  'make build-gpd  Check the νGpd examples' \
	  'make clean  Remove local Agda interfaces and generated Haskell output'
