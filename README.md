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

The coherences of the Bonak construction decompose recursively, in the same way at both coherence levels: a frame coherence is assembled from a frame coherence, recursively, and a layer coherence; a painting coherence from a layer coherence and a painting coherence, recursively; and a layer coherence from painting coherences and a frame coherence one homotopy level up, which at the truncation level is supplied by the truncation itself (UIP in the Rocq implementation). In Rocq each of these steps is a decomposition lemma; in Cubical Agda a path in a Σ-type is a pair of paths under an interval lambda, so the level-1 assemblies and, with the compiler patch used on this branch, the level-2 frame assembly are definitional. The dependent level-2 painting assembly and the layer closings remain lemmas:

| coherence | Rocq | this port |
|---|---|---|
| coh-frame | `eq_existT_curried` | definitional pairing |
| coh-painting | `eq_existT_curried_dep` | definitional pairing |
| coh-layer | `rew_cohLayer33` | `cohLayer-squareP` (`Bonak/RewLemmas.agda`) |
| coh2-frame | `eq_existT_curried_hex` | Definitional pairing |
| coh2-painting | `eq_existT_curried_dep_hex` | `Σ≡hex.Dep.hexᵈ` (`Bonak/GpdLemmas.agda`) |
| coh2-layer | `rew_coh2Layer` | `coh2Layer-cubeP` (`Bonak/GpdLemmas.agda`) |

At level 2 the frame square pairs its recursive frame and layer squares directly: ordinary path composition in a Σ-type computes componentwise. The painting square still needs a boundary filling, since dependent path composition in a varying Σ-type does not compute componentwise. Its interior is the pair of the layer and recursive painting squares; `compPathP-pairΣ` connects that pair to the required composite faces. The layer closings are where the truncation enters: `cohLayer-squareP` fills the level-1 square in the HSet of frames, and `coh2Layer-cubeP` fills the level-2 cube through `isGroupoid→Cube`, the cubical forms of the Rocq implementation's UIP and GUIP discharges.

Self-contained: everything is built from the builtin cubical primitives collected in `Bonak/Prelude.agda`.

### Agda features used

- `--cubical` — the ambient theory: the coherences are `PathP`s, and the pasting kit and truncation sites are built from `transp`/`hcomp` fillers via `Bonak/Prelude.agda`.
- `--rewriting` — `Bonak/NatRew` proves `p + zero ≡ p` and `p + suc k ≡ suc (p + k)` and registers them as rewrite rules, making addition definitional on both arguments; this is what lets the prefix formers re-split the same prefix as the tower trades `p` against `k`.
- `--guardedness` — the full tower `νSets` is a coinductive record (`νSet→`) growing the finite prefixes one filler family at a time.
- `--termination-depth` — coherence statements mention members a bounded number of dimensions above their own, so the call matrices contain bounded increases; `Bonak/νSet.agda` composes them at depth 3 and `Bonak/νGpd.agda` at depth 4.
- `--prop` — the definitionally irrelevant `Prop` universe; the tower's own proof relations (`≤` and `EqN` in `Bonak/LeProp`) are `Set`-valued with irrelevance annotations (`.`), which keeps them transportable while retaining `SProp`-like conversion.

## Toolchain

This branch requires the [record hcomp patch](https://github.com/olympichek/agda/commit/73af34a10759777a858aad2835e0da2a7f69eb17), published on the [record-hcomp-patch compiler branch](https://github.com/olympichek/agda/tree/record-hcomp-patch) and based on [Agda commit b9097ba](https://github.com/agda/agda/commit/b9097ba1608d3f564e0e2b8d20ac73ff63374757). The patch uses `hcomp` for record fields whose types and universe levels are independent of the composition direction. The Sigma instance was proposed in [Agda issue #5885](https://github.com/agda/agda/issues/5885), following Huber's composition rule. The compiler revision tested with this branch is `73af34a10759777a858aad2835e0da2a7f69eb17`; an unpatched release or nightly cannot check this branch.

Starting from a bare machine, [GHCup](https://www.haskell.org/ghcup/) provides the Haskell toolchain. Clone the compiler outside this repository: `agda-record-hcomp --build-library` checks every Agda file under the library root, so the compiler's own test files must not land there.

```sh
ghcup install ghc 9.12.2
ghcup install cabal 3.18.1.0 --set
cabal update
git clone --branch record-hcomp-patch --single-branch \
  https://github.com/olympichek/agda.git "$HOME/agda-record-hcomp-patch"
cd "$HOME/agda-record-hcomp-patch"
cabal install exe:agda -w ghc-9.12.2 --program-suffix=-record-hcomp \
  --installdir="$HOME/.local/bin" --overwrite-policy=always
export PATH="$HOME/.local/bin:$PATH"
```

This installs `agda-record-hcomp` alongside any existing `agda`. To reproduce the tested compiler exactly, run `git checkout 73af34a10759777a858aad2835e0da2a7f69eb17` in the compiler checkout before `cabal install`. The `-w` option selects the GHC version; use `$HOME` in the install directory because the shell does not expand `~` inside `--installdir=`.

Use fresh project interfaces when switching between stock and patched compilers: start with a fresh Bonak worktree or remove its `_build/` cache. Interfaces are cached by Agda version, which need not distinguish a patched compiler from its stock counterpart. Likewise, do not point `Agda_datadir` at a stock compiler's primitive library; its interfaces must be generated by the patched compiler.

### Editor

Configure the VS Code extension [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode) to use the custom executable:

```json
"agdaMode.connection.paths": ["/home/<user>/.local/bin/agda-record-hcomp"]
```

Replace `<user>` with your login name. Give the absolute path because the extension host does not necessarily inherit the shell's `PATH`. Run "Agda: Restart" after changing the setting. Using only the patched executable in this list avoids falling back to an incompatible stock compiler.

## Building

From the Bonak worktree root, check the whole library with:

```sh
agda-record-hcomp --build-library
```

This checks every module the `.agda-lib` includes. To check the two example roots individually, each with its imports:

```sh
agda-record-hcomp examples/Examples.agda
agda-record-hcomp examples/ExamplesGpd.agda
```

The first checks the nu-set examples and the second checks the nu-groupoid examples.
