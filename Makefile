.DEFAULT_GOAL := build

AGDA ?= agda-nightly
AGDA_FLAGS ?=
GHC_VERSION ?= 9.12.2
CABAL_VERSION ?= 3.18.1.0
AGDA_REF ?= nightly
PREFIX ?= $(HOME)/.local

# The two roots share expensive dependencies and Agda's interface cache.
.NOTPARALLEL:
.PHONY: build build-set build-gpd install clean help

build: build-set build-gpd

build-set:
	"$(AGDA)" $(AGDA_FLAGS) examples/Examples.agda

build-gpd:
	"$(AGDA)" $(AGDA_FLAGS) examples/ExamplesGpd.agda

install:
	ghcup install ghc "$(GHC_VERSION)"
	ghcup install cabal "$(CABAL_VERSION)" --set
	cabal update
	@set -eu; \
	mkdir -p "$(HOME)/.cache/cubical-bonak" "$(PREFIX)/bin"; \
	source_dir=$$(mktemp -d "$(HOME)/.cache/cubical-bonak/agda.XXXXXXXX"); \
	printf 'Building Agda in %s\n' "$$source_dir"; \
	curl --fail --location --retry 3 \
	  "https://github.com/agda/agda/archive/$(AGDA_REF).tar.gz" \
	  --output "$$source_dir/source.tar.gz"; \
	tar -xzf "$$source_dir/source.tar.gz" -C "$$source_dir" --strip-components=1; \
	cd "$$source_dir"; \
	cabal install exe:agda -w "ghc-$(GHC_VERSION)" --program-suffix=-nightly \
	  --installdir="$(PREFIX)/bin" --overwrite-policy=always

clean:
	rm -rf _build MAlonzo
	find Bonak examples -type f -name '*.agdai' -delete

help:
	@printf '%s\n' \
	  'make [build]  Check both example roots and their library dependencies' \
	  'make build-set  Check the νSet examples' \
	  'make build-gpd  Check the νGpd examples' \
	  'make install  Install the Haskell toolchain and build agda-nightly (needs GHCup)' \
	  'make clean  Remove local Agda interfaces and generated Haskell output' \
	  'Overrides: AGDA, AGDA_FLAGS, GHC_VERSION, CABAL_VERSION, AGDA_REF, PREFIX'
