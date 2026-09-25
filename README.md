# Cubical Bonak

A Cubical Agda port of [Bonak](https://github.com/artagnon/bonak).

Bonak began as a construction of indexed semi-simplicial sets in Rocq and has grown in two directions. One is research on the semi-simplicial types problem — constructing untruncated semi-simplicial objects, with their coherences, inside type theory — which is what the νGpd construction pursues. The other is building a library of simplicial and cubical sets carrying various structure, to support research on models of different flavors of univalent type theory, e.g. Cubical or Higher Observational; hence the construction is abstract in its arity, covering semi-simplicial (unary) and semi-cubical (binary) sets uniformly.

This port builds on three lines of work:

- The original Bonak, implemented in Rocq by Hugo Herbelin and Ramkumar Ramachandra, and its papers: [*A Parametricity-Based Formalization of Semi-Simplicial and Semi-Cubical Sets*](https://arxiv.org/abs/2401.00512) and [*The Very Dependent Recursive Structure of Iterated Parametricity in Indexed Form*](https://arxiv.org/abs/2602.12689).
- [Alice Laroche's Agda port](https://github.com/alicelaroche/bonak-agda) of the construction.
- Astra Kolomatskaia's work on displayed type theory and on the permutahedral coherences of semi-simplicial types: [*Displayed Type Theory and Semi-Simplicial Types*](https://arxiv.org/abs/2311.18781) (with Michael Shulman), [*You Wouldn't Permutahedron*](https://arxiv.org/abs/2407.10891), and her [perm](https://github.com/FrozenWinters/perm) repository.

The motivation specific to this port is to investigate whether Cubical Agda lets the coherences of Bonak's indexed construction take exactly the shape Kolomatskaia's permutahedral analysis predicts.

## Contents

The νSet tower (`Bonak/νSet.agda`) uses **fillers-only storage** with relative `(p , k)` indexing — only the fillers are stored, and every other notion is a function in one mutual block — and **PathP-shaped coherences**, stated as dependent paths over the frame coherence.

The **νGpd tower** (`Bonak/νGpd.agda`) sits on the same base: HGpd-valued frames/layers/paintings, the 2-coherences (coh2), and one truncation site (`isGroupoid→Cube`). Its pasting kit is `Bonak/GpdLemmas.agda`, whose fused closing lemma `coh2Layer-cubeP` checks the layer 2-coherence once over abstract families.

### The recursive structure of the coherences

The coherences of the Bonak construction decompose recursively, in the same way at both coherence levels: a frame coherence is assembled from a frame coherence, recursively, and a layer coherence; a painting coherence from a layer coherence and a painting coherence, recursively; and a layer coherence from painting coherences and a frame coherence one homotopy level up, which at the truncation level is supplied by the truncation itself (UIP in the Rocq implementation). In Rocq each of these steps is a decomposition lemma; in Cubical Agda a path in a Σ-type is a pair of paths under an interval lambda, so the level-1 assemblies are definitional and only their level-2 forms and the layer closings remain lemmas:

| coherence | Rocq | this port |
|---|---|---|
| coh-frame | `eq_existT_curried` | definitional pairing |
| coh-painting | `eq_existT_curried_dep` | definitional pairing |
| coh-layer | `rew_cohLayer33` | `cohLayer-squareP` (`Bonak/RewLemmas.agda`) |
| coh2-frame | `eq_existT_curried_hex` | `Σ≡hex.hex` (`Bonak/GpdLemmas.agda`) |
| coh2-painting | `eq_existT_curried_dep_hex` | `Σ≡hex.Dep.hexᵈ` (`Bonak/GpdLemmas.agda`) |
| coh2-layer | `rew_coh2Layer` | `coh2Layer-cubeP` (`Bonak/GpdLemmas.agda`) |

At level 2 the single-cell faces and the interior still pair definitionally; the hex lemmas assemble squares whose composite faces are compositions of pairings, and exist because `∙-pairΣ` (Rocq's `eq_trans_eq_existT_curried`) is the one Σ≡-composition law that is propositional rather than definitional in Cubical Agda. The layer closings are where the truncation enters: `cohLayer-squareP` fills the level-1 square in the HSet of frames, and `coh2Layer-cubeP` fills the level-2 cube through `isGroupoid→Cube`, the cubical forms of the Rocq implementation's UIP and GUIP discharges.

Self-contained: everything is built from the builtin cubical primitives collected in `Bonak/Prelude.agda`.

### Agda features used

- `--cubical` — the ambient theory: the coherences are `PathP`s, and the pasting kit and truncation sites are built from `transp`/`hcomp` fillers via `Bonak/Prelude.agda`.
- `--rewriting` — `Bonak/NatRew` proves `p + zero ≡ p` and `p + suc k ≡ suc (p + k)` and registers them as rewrite rules, making addition definitional on both arguments; this is what lets the prefix formers re-split the same prefix as the tower trades `p` against `k`.
- `--guardedness` — the full tower `νSets` is a coinductive record (`νSet→`) growing the finite prefixes one filler family at a time.
- `--termination-depth` — coherence statements mention members a bounded number of dimensions above their own, so the call matrices contain bounded increases; `Bonak/νSet.agda` and `Bonak/νGpd.agda` both check at depth 3.
- `--prop` — the definitionally irrelevant `Prop` universe; the tower's own proof relations (`≤` and `EqN` in `Bonak/LeProp`) are `Set`-valued with irrelevance annotations (`.`), which keeps them transportable while retaining `SProp`-like conversion.

## Toolchain

The tree checks with Agda 2.8.0; the preferred toolchain is an Agda 2.9.0 nightly, which carries the interface-pass fix for the νGpd pasting kit's large telescopes. In cold sequential builds of the same checkout on the same machine, the νGpd tower took approximately 39 minutes with Agda 2.8.0 and 5.5 minutes with the nightly. The nightly is built from the source archive of Agda's rolling `nightly` tag.

Starting from a bare machine, [GHCup](https://www.haskell.org/ghcup/) provides the Haskell toolchain; the versions below are the ones this sequence is verified with, and the nightly's own `tested-with` currently spans GHC 9.4 through 9.14. Unpack the archive anywhere outside this repository — `agda --build-library` checks every Agda file under the library root, so the compiler's own test files must not land there — and install from the unpacked directory:

```sh
ghcup install ghc 9.12.2
ghcup install cabal 3.18.1.0 --set
cabal update
curl -L https://github.com/agda/agda/archive/refs/tags/nightly.tar.gz | tar xz
cd agda-nightly
cabal install exe:agda -w ghc-9.12.2 --program-suffix=-nightly \
      --installdir="$HOME/.local/bin" --overwrite-policy=always
```

That leaves `agda-nightly` on the PATH beside whatever `agda` is. `-w` selects the GHC version; write the install directory with `$HOME`, since the shell does not expand `~` inside `--installdir=`. The tag moves with master; to pin a commit, download `archive/<sha>.tar.gz` instead (it unpacks to `agda-<sha>`). Keeping the unpacked directory allows incremental rebuilds across nightly bumps: run `cabal build exe:agda -w ghc-9.12.2` there, obtain the binary's path with `cabal list-bin exe:agda`, and symlink it as `agda-nightly`. Interfaces are cached per Agda version under `_build/<version>/agda/`, so a release and a nightly can be used alternately while keeping each other's caches intact.

### Editor

The VS Code extension [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode) chooses its Agda from the `agdaMode.connection.paths` list, trying the entries from the last to the first, so appending the nightly makes it the one used:

```json
"agdaMode.connection.paths": ["agda", "/home/<user>/.local/bin/agda-nightly"]
```

Give the absolute path: the extension host does not necessarily inherit the shell's `PATH`, so a bare `agda-nightly` may fail to resolve. The `Ctrl+X Ctrl+S` command in an Agda buffer edits the same list interactively, and "Agda: Restart" replaces the running Agda after a change.

## Building

```sh
agda-nightly --build-library
```

checks every module the `.agda-lib` includes. Individual roots check with `agda-nightly examples/Examples.agda` (the νSet examples) and `agda-nightly examples/ExamplesGpd.agda` (the νGpd examples), each pulling in what it imports.
