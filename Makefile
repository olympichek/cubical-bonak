.DEFAULT_GOAL := build

AGDA ?= agda
AGDA_FLAGS ?=
AGDA_RELEASE := v2.9.0
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
	@set -eu; \
	case "$$(uname -s)/$$(uname -m)" in \
	  Linux/x86_64) platform=linux; sha=a9f9b19dc911b363e97f7f7938ae642d02e814f71d2e1eec5428825f1aede786 ;; \
	  Darwin/arm64) platform=macOS-arm64; sha=7865f46ce9eba13b2620405a59b2316ce38ec3b14a50a860546f45173a82d343 ;; \
	  Darwin/x86_64) platform=macOS-x64; sha=0c983a545ebabe83a9284fa3b87aab7d6cbd2168b9b88c2ca12abe567536b1ea ;; \
	  *) echo 'No matching release binary; install Agda 2.9.0 manually and run make.' >&2; exit 1 ;; \
	esac; \
	dir=$$(mktemp -d); trap 'rm -rf "$$dir"' EXIT; \
	curl --fail --location --retry 3 --output "$$dir/agda.tar.xz" \
	  "https://github.com/agda/agda/releases/download/$(AGDA_RELEASE)/Agda-$(AGDA_RELEASE)-$$platform.tar.xz"; \
	if command -v sha256sum >/dev/null; then \
	  digest=$$(sha256sum < "$$dir/agda.tar.xz"); \
	else \
	  digest=$$(shasum -a 256 < "$$dir/agda.tar.xz"); \
	fi; \
	[ "$${digest%% *}" = "$$sha" ] || { echo 'Agda archive checksum mismatch' >&2; exit 1; }; \
	tar -xJf "$$dir/agda.tar.xz" -C "$$dir"; \
	mkdir -p "$(PREFIX)/bin"; \
	install -m 755 "$$dir/agda" "$(PREFIX)/bin/agda"

clean:
	rm -rf _build MAlonzo
	find Bonak examples -type f -name '*.agdai' -delete

help:
	@printf '%s\n' \
	  'make [build]  Check both example roots and their library dependencies' \
	  'make build-set  Check the νSet examples' \
	  'make build-gpd  Check the νGpd examples' \
	  'make install  Install the official Agda 2.9.0 release binary' \
	  'make clean  Remove local Agda interfaces and generated Haskell output' \
	  'Overrides: AGDA, AGDA_FLAGS, PREFIX'
