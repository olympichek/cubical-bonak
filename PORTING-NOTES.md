# cubical-bonak porting notes / resume kit

Goal: three Cubical Agda ports of Bonak νSet+νGpd — V1 direct mirror
(`main`), V2 PathP-native (worktree `../pathp`), V3 groupoid-rew
(worktree `../rew`). Agda perf track: build Agda from source, profile,
backport Rocq conversion-cache ideas (`~/rocq` conv-instrument, 22x).

## Status (2026-08-12)

- **V1 νSet: DONE.** `Bonak/νSet.agda` typechecks (~5 min hot spot:
  `mkCohPainting` — same intrinsic-defeq hotspot as Rocq/Lean).
  Gate: `Bonak/Examples.agda` — SemiSimplicial4 normalizes (~30KB)
  with transp/hcomp residue on neutral painting fibers (probe G3
  wart). V2/V3 target exactly that residue.
- **V1 νGpd: IN PROGRESS** (nothing written yet; sources read).
- Agda master (2.9.0-dev, commit 5c29d3e) building in background with
  GHC 9.12.2 (`~/agda-dev/src`; 9.14.1's base too new for deps).

## Load-bearing design decisions (V1)

1. **Layers are functions** (user directive): `Layer B = (ε:arity)→B ε`;
   LayerSig/LayerGpdSig collapse to the `arity : Set` module parameter.
   `nth`=app, `lam`=id, `ext`=funExt (definitional round trip). The
   Rocq theory fact "no 2-element-arity layer former has definitional
   nth∘lam AND provable ext" dissolves in cubical. r=0 case of
   `mkCohPainting` becomes `refl` (Rocq needed `nth_lmap`).
2. **≤ is Set-valued recursive into η-⊤/⊥ with irrelevant (.) proof
   args everywhere** (`Bonak/LeProp.agda`). NOT Prop: `--prop` +
   indexed match ⇒ CannotGenerateTransportClause (probes/P01, gate 1).
   Dot-irrelevance restores SProp-like conversion (P01 gate 4).
   `suc n ≤ suc m` REDUCES to `n ≤ m`, so Rocq's ⇑/⇓ vanish; use
   `le-trans`/`le-up`/`le-down` (explicit ℕ args — ≤ is a defined
   function, not unification-invertible; implicit versions ↕/↑/↓ exist
   but fail inference at tower call sites).
3. **Block classes → `interleaved mutual`** (user directive):
   mkRestrFrameTypes⋈mkFrames (+mkLayer taking the Σ-components of R
   separately so its signature needs no reduction), and
   mkCohFrameTypes⋈mkRestrFrames. `mkRestrLayer` abstracts prevRF +
   its r=0 coherences as args (like Rocq's `prev` block) — keeps it
   out of the termination clique.
4. **Deps\* classes → η-records** (constructors `depsRestr`, `depsCohs`,
   `depsCohs2`). All Rocq `.(1)`-convertibility facts
   (π₁D (mkDepsRestr dc) ≡ mkDepsRestr (π₁C dc) etc.) hold
   definitionally via η + clause unfolding. `toDepsRestr/toDepsCohs`
   need their implicits EXPLICIT at call sites (stuck-function
   unification); `mkDepsRestr` inlines the record constructor.
5. **Extension inductives**: p is an index (non-uniform parameter in
   Rocq). Indexed matches emit UnsupportedIndexedMatch warnings
   (benign: all our scrutinees are literal constructors; functions
   won't compute on TRANSPORTED extension values only).
6. **SigT kit → PathP pairing + toPathP/fromPathP**
   (`Bonak/RewLemmas.agda`): `Σ≡` (=eq_existT_curried), `Σ≡dep`
   (=eq_existT_curried_dep), substComposite, substCommSlice
   (=map_subst), `rew-cohLayer33` proved by a subst-chain.
   `Π-subst-ext` replaces the Layer.v bridges (lmap2_rew_eq etc.).
7. **UIP→isSet**: mkCoh2Frame = `isSetDom (snd (dFrames …)) _ _ _ _`.
8. Implicits that Agda cannot infer and must be given explicitly:
   Σ≡dep's P/Q at mkCohPainting; Π-subst-ext's B at mkCohLayer;
   substCommSlice's P inside rew-cohLayer33.
9. **The mkCohLayer proof term is consumed definitionally** by
   mkCohPainting (Σ≡dep's H/Hu must be byte-identical to what
   mkCohFrames stored — same discipline as Rocq/νPermSet).

## νGpd V1 roadmap (next)

Sources: `theories/νSet/νGpd.v` (1179 l) + `νGpd/{HGpd,Layer,Lemmas}.v`
at bonak master. Structure = νSet one storey up: HSet→HGpd,
coh2Frame/coh2Painting become STORED data (Coh2FrameTypeBlock,
DepsCohs3, mkCoh2Layer, mkCoh2Painting), GUIP only at the top.

1. Prelude additions: `isGroupoid`, `isSet→isGroupoid`,
   `isGroupoidΣ` (needs isSetRetract — port retract_UIP; the Σ-path
   space iso is DEFINITIONAL in cubical, both round trips),
   `isGroupoidΠ` (direct, like isSetΠ),
   `isGroupoid→isSetPathP` (like isSet→isPropPathP), `HGpd` record
   (`gset`? name: `hgpd`), `gunit`, `gΣ`, `gΠ`, `hpaths : HGpd → HSet`.
   No Hedberg needed (isSet⊤ → isGroupoid ⊤ by cumulativity).
2. SigT kit extension (RewLemmas or new GpdLemmas.agda):
   `sigT-map-eq` (=sigT_map_eq: subst Q (cong f p) (g x u) ≡ g y v),
   `⊙` (=sigT_trans_eq), their computation laws
   (sigT_map_eq_refl, f_equal_eq_existT_curried,
   eq_trans_eq_existT_curried, sigT_map_eq_existT_curried_dep_curried,
   sigT_trans_eq_existT_curried_dep, eq_existT_curried_eq,
   eq_existT_curried_dep_eq), then `Σ≡hex`
   (=eq_existT_curried_hex) and `Σ≡dep-hex`
   (=eq_existT_curried_dep_hex). All proofs are J-chains (destructs).
3. The two big νGpd/Lemmas.v lemmas: `permutahedral_coherence`
   (7-hexagon pasting; conclusion = the HHA hexagon) and
   `rew_coh2Layer` (~40 premises; kc/kb/k-naming = the "stored data
   as definitional unfoldings" premises), `rew_coh2Painting_restr0`.
   Proofs: long generalize+destruct chains → J-chains in cubical.
   These are self-contained path algebra — delegable.
4. νGpd.agda: copy νSet.agda skeleton, swap HSet→HGpd, add the extra
   storey: mkCohFrameType (now abstract commuting-square TYPE),
   mkCoh2FrameType (stored hexagon data, was PROVED by UIP in νSet),
   Coh2FrameTypeBlock mutual (mkCoh2FrameTypes⋈mkCohFrames),
   mkCohLayerType/mkCohLayer, DepsCohs3 + extension + mkExtraCohs2,
   mkCoh2Painting* endpoint-type machinery (νGpd.v:653-754),
   mkCoh2Layer (846), mkCoh2Frames (921), mkCoh2Painting (1003),
   νGpdData (1091). GUIP use: search νGpd.v for the top truncation
   site.
5. Gate: SemiSimplicial5-analogue (νGpd examples at arity ⊤).

## Perf notes

- Full νSet.agda recheck ~5 min (Agda 2.8.0, -O2 build). Hot:
  mkCohPainting + mkCohLayer conversion. Profile with
  `agda --profile=definitions` once νGpd lands.
- Rocq ideas to backport: fid-keyed conversion cache (~/rocq
  conv-instrument, 22x on SemiSimplicialGpd), `exact_no_check`
  analogue (Agda has no such escape; maybe postulate+rewrite trick or
  --allow-unsolved + later check), sharing in transp-normal forms.

## Measurements (2026-08-12, Agda 2.8.0, this machine)

νSet.agda full check: **V1 (mirror) ~5:10** / **V2 (PathP) 2:35** /
**V3 (rew) 8:19**. V1 profile (--profile=definitions): mkCohPaintings
212s + mkExtraCohs 91s = 98% — the π₁-commutation conversions
(mkExtraCohs (AddCoh2Dep …) ≡ AddCohDep …, fst (mkRestrPaintings …) ≡
Prefix …), NOT mkCohPainting itself (2.9s). --profile=internal: all in
Typing.CheckRHS. V2 wins by eliminating Σ≡/Σ≡dep/toPathP (definitional
PathP pairing); V3's ∙ᵗ chains cost extra at νSet level (payoff
expected only where coh2 is stored data).

νGpd parts 1-2 (νSet cached): V2 and V3 both 27s. V1 νGpd with the
DepsCohs2 storey + mkCohPainting: check exceeded 30 min CPU (running;
the Σ≡dep alignment conversion blows up at groupoid level). If it
does not converge: introduce named type wrappers (νGpd.v:692's
goal-folding trick) or land the conversion cache first.

Conclusion so far: **the direct mirror (V1) is the most expensive of
the three to typecheck, and the PathP-native V2 is the cheapest** —
the conversion burden tracks how much transport-reshuffling glue
(toPathP/Σ≡dep/∙-assoc) sits in the proof terms.


## THE ETA FIX (2026-08-12, headline)

`no-eta-equality; pattern` on the three Deps records (+ pinning ONE
implicit that η used to solve: TopRestrDep's deps in mkνSetData)
collapses all typecheck times to Rocq-comparable:

| file                        | with η        | no-eta |
|-----------------------------|---------------|--------|
| V1 νSet                     | 310 s         | 5.1 s  |
| V2 νSet (PathP)             | 155 s         | 3.9 s  |
| V3 νSet (rew)               | 499 s         | 5.8 s  |
| V1 νGpdBase                 | 28 s          | 1.5 s  |
| V1 νGpd DepsCohs2 storey    | >40 min, DNF  | 3.4 s  |
| V2/V3 νGpd parts 1-2        | 27 s          | ~1.3 s |

(Rocq νSet.v: 1.85 s.) Diagnosis: Agda's conversion eta-expands record
comparisons (621k of 6.19M compares) — each expansion multiplies a
comparison by the field count and duplicates the neutral spine, giving
combinatorial blowup down the Deps tower; conversion count dropped
6.19M → 38k. Rocq's primitive projections have η too, but its lazy
kernel shares the spine. Our builders are constructor-headed, so η was
never load-bearing for the tower's definitional equalities.

Both compute gates (SemiSimplicial4 normalization, Examples) still
pass. The conversion-cache Agda patch (~/agda-dev/src, enable with
AGDA_CONVERSION_CACHE=1) is superseded as a necessity but kept as an
artifact; A/B against the eta-fixed code is optional follow-up.
