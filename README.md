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
- `--termination-depth` — coherence statements mention members a bounded number of dimensions above their own, so the call matrices contain bounded increases; `Bonak/νSet.agda` checks at depth 2 and `Bonak/νGpd.agda` at depth 3.
- `--prop` — the definitionally irrelevant `Prop` universe; the tower's own proof relations (`≤` and `EqN` in `Bonak/LeProp`) are `Set`-valued with irrelevance annotations (`.`), which keeps them transportable while retaining `SProp`-like conversion.

## Building

We recommend [Agda 2.9.0](https://github.com/agda/agda/releases/tag/v2.9.0) because it includes a [compiler fix](https://github.com/agda/agda/pull/8675) that speeds up the νGpd build.

With Agda installed and `agda` on your `PATH`, run the following from the repository root:

```sh
agda --version
make
```

`make` checks the νSet and νGpd examples and their dependencies. Use `make build-set` or `make build-gpd` to check just one, and `make clean` to remove generated files.
