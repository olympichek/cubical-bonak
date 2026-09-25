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
   indexed match ⇒ CannotGenerateTransportClause (agents/probes/P01, gate 1).
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

## Proposed V4: fillers-only storage + `(p,k)` indexing (2026-08-13)

Not a variant of V1's *equalities* (that is V2/V3) but of its *storage*.
V1 mirrors Rocq: four `Deps*` η-records holding frames, paintings,
restrictions and coherences. Alice's `agda-alice` stores **only the
fillers** and computes everything else as functions of one mutual block:

```agda
νSet-< zero    = ⊤
νSet-< (1+ n)  = Σ[ R ∈ νSet-< n ] νSet-= n R
νSet-= n D     = frame n n (◆₂ n) D .Dom → HSet
```

`frame`, `layer`, `painting`, `restr-{frame,layer,painting}`,
`coh-{frame,layer,painting}` are the other nine members of that block —
functions of the indices and of `D` (`agda-alice/src/νSet/Base.agda:30-104`).
V4 = **Alice's storage discipline, master's index discipline.**

### The design

1. **Store only fillers.** `Pre`/`Fil` as above; everything else a
   function. This extends V1 decision 3 (`Block classes → interleaved
   mutual`) from the individual Blocks to the whole construction — the
   `Deps*` records of decision 4 disappear rather than being encoded.
2. **Keep `(p,k)`,** `n = p + k` never named. Bounds stay as V1 decision
   2 (Set-valued recursive `≤`, dot-irrelevant proof args). Unchanged.
3. **One generic chain** for descent (see costs below).

### Why the combination, and not either half

The two designs pay on *different* axes, and each kills the other's main
expense.

Fillers-only kills the zipper. With one stored family instead of four
there is nothing to map *between*: in the Rocq line the four record types
force nine image maps (`extChainDeps`, `cohsChain{Ext,Next,Deps,Next1,
Extend,NextExt}`, `cohs2Chain{Cohs,DepsCohs}`) plus a 126-line algebra
section proving they commute with composition and extension —
`indexed-fibered-eq/theories/νSet/Equiv/Face.v`. The same skeleton is
re-stamped per extension: ~58% of `νDgnSet` is repeated zipper, and
`Equiv/` mirrors it three times (presheaf-side, translation-side, chains).
None of that gets built.

`(p,k)` kills the inequality layer. The difference *is* the index, so
there are no `[_≤_][_]₂/₃/₄` records, no stored `δpn`/`δqn`, no coherences
between differences, no `drop₃-*`/`drop₄-*`, and **no `recover-nat-eq`**
(15 sites in agda-alice: 8 `νSet/Face.agda`, 4 `Correspondence.agda`, 3
`νSet/Base.agda`) — at `j = 0` the source type *is* the target type.
`Inequalities.agda` 192 lines vs `LeProp`-style ~90.

Note this is **not** an SProp story. Agda's dot-irrelevance already does
what SProp does, and Alice uses it (`.Hpn`). Her ₂/₃/₄ records exist
because *absolute* indices must reconstruct their pairwise differences,
and those differences are relevant by necessity — she recurses on `δ`, and
you cannot recurse on an irrelevant argument any more than on an SProp.

| | agda-alice | V1 (Rocq mirror) | **V4** |
|---|---|---|---|
| zipper records | none | four `Deps*` | none |
| image maps + algebra | none | inherited from Rocq | none |
| inequality layer | 192 lines | ~90 | ~90 |
| `recover-nat-eq` sites | 15 | 0 | 0 |
| descent | free (one index moves) | chains ×4 | one generic chain |

### The one real cost: descent needs reification

`(p,k)` moves **both** indices under a step, so relating stages
arithmetically is impossible. Probed twice, in Rocq:

- numerically — `projSteps (j : ℕ) : I (j + p) k → I p (j + k)` fails with
  `j0 + k.+1` vs `j0.+1 + k`, and no `Nat.add` orientation fixes it (the
  source needs left-recursion, the target right-recursion);
- in the Moore idiom — replacing nats by lists and addition by
  concatenation reproduces it verbatim as `js ++ (x ∷ L)` vs
  `x ∷ (js ++ L)`.

The obstruction is **reversal**, not associativity: descending moves items
from one index to the other, flipping order. Moore chains make
associativity definitional and do not touch this. So no representation
trick removes it — with one moving index (absolute `(n,p)`) descent is a
three-line fixpoint; with two, it must be reified.

Cheap, because there is now only one index family:

```agda
data GChain {I : ℕ → ℕ → Set} (step : ∀ p k → I (suc p) k → I p (suc k))
            {P K} (top : I P K) : ∀ {p k} → I p k → Set where
  nil  : GChain step top top
  cons : ∀ {p k} {x : I (suc p) k} → GChain step top x → GChain step top (step p k x)
```

Verified in Rocq: all three of master's projection chains instantiate this
single family, with `compose` and `length` proved once generically.
~25 lines total, against four families + nine images + 126 lines of algebra.

### Risks, cheapest probe first

1. **The eta fix loses its target.** THE ETA FIX above is
   `no-eta-equality; pattern` on *the three `Deps` records* — V4 deletes
   them. Either the blowup cannot arise (no record η to expand in the
   tower) or it reappears on the prefix `Σ`, where there is no equally
   clean lever. **Probe this first**, before writing any tower: build the
   fillers-only `Pre`/`Fil`/`Frame`/`Layer` block to level 2 and compare
   conversion counts against V1's 38k/6.19M.
2. **Termination depth.** Whole-construction mutual is larger than V1's
   per-Block `interleaved mutual`; agda-alice needs
   `--termination-depth=3` for an 11-symbol fillers-only block. Budget for
   raising it — it is a per-file global pragma, not a local annotation.
3. **Index-translation tax, permanent.** The paper and agda-alice are
   absolute; every cross-check goes through `~/bonak/notes/index-translation.md`.
   This is not free: the `νDgnSet` Below/Above base shift (§2, §5 of that
   note) is exactly where it bites, and it is easy to mis-attribute
   structure to indexing that is really intrinsic to degeneracies (the
   Below/Above split appears in absolutely-indexed `dgn-alice` too).
4. **Unvalidated:** whether V1 decision 4's `.(1)`-convertibility facts
   survive. They currently come from clause unfolding of constructor-headed
   builders; with functions instead of records they should come from clause
   unfolding of the mutual block, but that is reasoning, not a measurement.

### Review findings (2026-08-14)

Design review against `~/bonak/notes/index-structures.md` (same day:
the dimension-vs-algebra split, the one-variable law `S^a(x)`, and the
bound-vs-inventory division of labor). Verdict: sound; V4 is the
fourth quadrant of the storage × indexing square, and the
cost-complementarity claim holds up. Refinements:

1. **The reversal obstruction is an instance of the one-variable
   law**: `projSteps` puts two open variables in every index position,
   violating `S^a(x)` on both coordinates at once. Confirms that no
   representation trick removes it and reification is the correct
   response.
2. **`GChain` is the proof-relevant free ≤** (`le_refl`/`le_up` with
   the proof carrying step views). That encoding is dominated by
   irrelevant bounds *for bounds* — it earns its keep exactly and only
   where the proof is needed as data, which descent is. Coordinates
   stay unary + irrelevant; the path gets the constructor spine.
3. **Probe 1 re-scoped.** (a) Probe at level 4, not level 2 — every
   conversion cliff in this tower's history (the eta fix, the
   `mkExtraCohs` commutations, Rocq `Defined` times) appeared at
   dimension 4–5. (b) Alice's prefix is an iterated Σ, and Σ has
   definitional η with no `no-eta-equality` lever: include a variant
   with `Pre` as a per-level no-eta record (`_∷_`-style, like the
   coinductive `νSet->`). (c) Add a **sharing axis** the proposal
   omits: stored `Deps*` records memoize strata, fillers-only
   recomputes `frame`/`painting` as function applications at every use
   site; the eta-fix diagnosis (η-expansion, not term size) suggests
   this is survivable, but agda-alice — the only fillers-only artifact
   ever measured — is the slowest of the three systems. Measure
   conversion counts AND wall time.
4. **Risk 4 promoted: it is the successor of the actual V1 hotspot.**
   The V1 profile put 98% of check time in π₁-commutation conversions
   (`mkExtraCohs`), not in `mkCohPainting`. V4 deletes those facts but
   creates their analogues: commutation of `GChain`'s generic
   `compose` with the block functions on **open** chains (inside
   recursive cases the chain argument is a variable, so `compose` is
   stuck). If decision 9's byte-identity discipline consumes these
   definitionally, this is where V4's conversion budget concentrates.
   The deciding question — `compose`-commutation *proved* vs *holding
   by clause unfolding* at the consuming sites — goes into the probe.
5. **Risk 2 may invert.** Alice's dimension is a projected record field;
   V4's is a bare `k : ℕ` in constructor position, which the
   termination checker reads directly. Hypothesis (untested): the
   block needs depth 2, not 3. Cheap to measure in the probe.
6. **Underspecified load-bearing detail: the type of `D`.**
   `frame p k D` needs a prefix of length `p + k`, which the
   discipline forbids naming — so `I p k` must be a *split*
   filler-prefix family whose re-splitting step is what `GChain`
   chains over. Implicit in `projSteps`' signature, never stated;
   needs a design paragraph before implementation (it is where the
   Rocq line pays with `DepsRestr`-vs-Extension and where the
   off-by-one conventions live).
7. **A third descent option is missing from the option space:
   CPS/accumulator descent** — build the downward strata as functions
   of the eventual top data during the upward pass, closing the
   continuation when the filler arrives; `compose` becomes function
   composition (definitional). Two Rocq experiments running 2026-08-14
   bear on this directly: the merged-single-extension refactor in the
   `single-block` worktree (= the `GChain` consolidation claim, Rocq
   side) and the CPS fusion probe in the `cps-fusion` worktree. CPS
   must fight Rocq's guard checker; if it survives there it is
   strictly easier in Agda. **Gate the descent-mechanism choice on
   both reports**; prototype descent both ways in the probe file
   before committing the mutual block to `GChain`.

   *Update (2026-08-14, later): the CPS report landed, green*
   (`~/bonak/cps-fusion/CPS-FUSION-REPORT.md`). Three findings that
   change the picture for V4:
   - **The continuation degenerated to first-order.** No accumulator
     fields, no higher-order data: each `Deps…` class stores the
     *single* datum the suffix determines at its level (the top
     painting / restrPainting family / cohPainting), and the `proj1`
     truncation instance *is* the step. All three Extension inductives
     and both global descent fixpoints deleted; `SemiSimplicial4`
     byte-identical; **1.7× faster** than baseline. So the real
     dichotomy for V4 descent is not GChain-vs-CPS but
     **chain-reification vs stored-top + step** — and stored-top won
     in Rocq. Note the tension with fillers-only: the Rocq win came
     from storing *one more computed field per level*, exactly what
     V4's storage discipline forbids; if fillers-only descent hurts,
     this is the measured fallback.
   - **The bottom index must stay out of the stored data**: the
     `q = 0` case (`nth l ε`) must remain a uniform wrapper around the
     stored `q.+1`-part, or the `r = 0` coherence case loses its
     definitional `nth` reduction at variable prefixes. Directly
     relevant to decision 9's byte-identity discipline.
   - **Index equalities become conversion problems** when an inductive
     index is replaced by a computed record: two invisible one-line
     choices (a stray `simpl.`, projecting a step out of a record
     instead of naming it) cost a factor of 11. Keep step terms
     syntactic at consuming sites.
   *Update (2026-08-14, latest): the merged-single-extension report
   landed too* (`~/bonak/single-block/SINGLE-BLOCK-REPORT.md`), green
   but decisive against chain-walking:
   - **One-chain-for-all-strata is refuted with a mechanized
     witness**: storing the strata-4–6 lists only at the far end makes
     every access a `k`-step walk, stuck under variable `k` (the
     `r = 0` coherence branch never exposes `nth`); nodes must carry
     increments, increments' types need the accumulated lists, whose
     types mention the strata-1–3 chain — the staircase is forced.
     `GChain`-style reification is viable only with
     increment-carrying nodes, and its `push`/`proj1` round-trips are
     definitional (record eta + primitive projections) — good news
     for the analogous Agda facts.
   - **Un-bundling is a 30× conversion regression** (1.7 s → ~50 s):
     replacing one record variable by 5–7 explicit arguments blows up
     what the kernel converts. Record bundles are load-bearing;
     V4's "delete the records" must not become "thread components".
   Head-to-head verdict: stored-top + step (three classes, zero
   chains, 0.96 s) beats increment-chain reification (one class,
   three chains, ~50 s) on every axis measured in Rocq.

### Build results (2026-08-14): V4 BUILT — 8× cheaper than V1

Worktree `../fillers-only` (branch `fillers-only`), full report
`V4-REPORT.md` there. All eleven members closed, no postulates; gate
passes with `frame 4` residue-free and `SemiSimplicial4` reproducing
V1's normal form (same 195 transp/hcomp — the G3 wart is confirmed to
live on the equality axis, so V2 stacks). Headlines:

- **V1 6.2 s / 37.9k conversions → V4(a) 0.77 s / 4.8k, V4(b) no-eta
  prefix 0.43 s / 3.9k** — ~8× on both axes, ~5× faster than V2.
  Tower ≈205 code lines vs Alice's 315 and V1's 621.
- **The decisive probe was not eta but the prefix length**: `frame p k`
  needs `Pre (p + k)` under three addition equations no recursive `+`
  satisfies together (the reversal obstruction, definitional form).
  Resolution: `--rewriting` with *proved* `+-zero`/`+-suc` REWRITE
  rules (cubical Path accepted as the relation) — then `I p k` is just
  `Pre (p + k)`, no split family. Caveat: the confluence checker skips
  `--cubical` (critical pairs joined by hand); conversion is genuinely
  extended, no Rocq analogue.
- **No reified descent of any kind was needed** — no GChain, no CPS,
  no stored-top, zero stage-commutation glue. The Rocq chains were an
  artifact of relating *stored strata* across stages; with nothing
  stored there are no stages to relate. Risk 4 (the mkExtraCohs
  hotspot's successor) does not materialize — the hotspot is deleted.
- **Eta**: the blowup does not return on the prefix (208 η-expansions
  vs V1's 393); the no-eta record prefix still buys 1.8×. Sharing
  axis: no recomputation penalty — agda-alice's slowness is hereby
  attributed to her Inequalities layer, not fillers-only storage.
- **The one open bill: termination is NOT established.** Depths 2–6
  all fail; six of eleven members carry `{-# TERMINATING #-}`. Cause
  is structural: the decreasing quantity is the prefix length
  `p + k` — a type-level expression, an argument of nothing; Alice
  passes because that level is her first argument. Column alignment
  and avoiding `where` blocks are load-bearing for the checker (see
  report §5, incl. a reconstructible partial fix costing four extra
  coherence arguments).

*Update (2026-08-15) — termination revisited, several §5 claims
corrected (report § "Termination revisited"):* the pragma attaches to
the WHOLE mutual block, so "six of eleven" was five redundant copies —
the file now carries exactly ONE pragma, which is also the floor for
any unchecked variant. The rejected cycle is a single ten-call loop
(`frame → frame → layer → restr-frame → restr-layer → coh-frame →
coh-layer → coh-painting → coh-painting → coh-layer → frame`);
deleting any one edge passes at any depth, but every edge is a
defining clause of the tower. **The prev-abstraction route is refuted**:
abstraction moves an edge to the caller and every caller is on the
loop (three abstractions modelled, verdict unchanged). Two mechanisms
isolated, each eliminated experimentally without changing the verdict:
`pre`/`fil` projections leaking into solved implicits (a pre-split
rewrite removes them: −9% conversions, +30% wall, still rejected, and
`frame` loses its variable-prefix reduction — not kept), and `Pre`
being a defined type rather than an inductive family
(`agents/probes/V4-P01-termination.agda`: the stripped ten-edge model is
ACCEPTED over a length-indexed `data Pre`, rejected over the function —
but the full block is rejected either way). The §5 `where`-block claim
is not reproducible. Trust posture: two hand-checked meta-obligations
(REWRITE confluence, one block-level termination pragma). The
remaining checked-termination route is checker-side: a synthetic
measure column (sum of nat arguments) in the agda-dev fork.

Recommendation adopted from the report: carry V4 as the storage
discipline for the νGpd storey, combined with V2's PathP equalities.

Layers-as-functions (decision 1) and the `≤` encoding (decision 2) are
orthogonal and carry over verbatim. So does the V2/V3 axis: V4 is about
what is stored, PathP/rew are about how equalities are represented, and the
four combine freely.

## Rocq backport of the dimension-column tower: refuted (2026-08-17)

`Bonak/νSetF.agda` (fillers-only + dimension columns, zero TERMINATING
pragmas) does not backport to Rocq: its termination is a size-change
argument (three families descending on three different columns,
strictness only around composed cycles) and Rocq's guard demands
per-call strict descent on the caller's single {struct} argument —
the call skeleton is rejected on its first edge. Restaging to satisfy
the guard re-derives the stored-strata Rocq original, Deps records
and all: the Rocq architecture is the guard-imposed normal form of
this construction, and the fillers-only block exists only under
size-change termination. The NatRew rewrite rules DO port (Symbol
addition under -allow-rewrite-rules, verified on bonak-patched-rocq /
Rocq 9.4+alpha), and EqN is LeSProp.v's pattern mirrored back.
Receipts: agents/probes/V4_P06_rocq_backport.v; full account: V4-REPORT.md
§8 of the output-dimension section.

## Dimension tower canonicalized (2026-08-17, later)

The dimension-column tower is the branch's canonical `Bonak/νSet.agda`:
`Bonak/νSetF.agda` and `agents/probes/ExamplesF.agda` are renamed to
`Bonak/νSet.agda` and `examples/Examples.agda`, and the 1-pragma tower
they sat beside is removed. No `{-# TERMINATING #-}` remains outside
the probes that exist to demonstrate it; the residue is
`--termination-depth=3` in the tower's OPTIONS. Earlier sections use
the pre-rename names.

## Branch surgery: main = V4 storage + V2 equalities (2026-08-17, latest)

The direct-mirror line is renamed `globular` (worktree `../globular`,
history unchanged); `main` now branches off `fillers-only` with the
coherences refactored to the PathP shapes of DESIGN-V2 — the adopted
V4 + V2 combination.  The axes compose as predicted:

- `coh-layer` / `coh-painting` are stated as PathPs over the frame
  coherence; no statement contains a subst.
- The Σ-assemblies in `coh-frame` and `coh-painting` are definitional
  pairing `λ i → (… i , … i)`; the Π-layer step is definitional.
- `coh-layer`'s body is one `cohLayer-squareP` (the PathP form of
  rew-cohLayer33) closed by `isSet→Square`; the r = 0 painting
  coherence is `subst-filler` of restr-layer's transport, which stays
  at the term level.

Vanish census at νSet level: the tower consumes {cohLayer-squareP,
isSet→Square, subst-filler} where the Id form consumed
{rew-cohLayer33, Π-subst-ext, Σ≡, Σ≡dep}.  The Id-form kit and the
subst lemmas under it (substComposite, substCommSlice, ∙-assoc, J)
are DELETED — RewLemmas is the PathP kit only — together with the
probes that exercised it: the P02 Σ≡-composition pair (live on
`globular`), V4-P05-dimension-no-proof (verdict recorded in V4-REPORT,
"Can the dimension column shrink?"), and the broken-header V4-P00-rewrite
(its REWRITE story lives in Bonak/NatRew.agda and the build-results
section above).  The pinned-implicit discipline carries
over unchanged: the goal still exposes the chain endpoints only after
unfolding two nested restr-layer clauses.

Measurements (Agda 2.8.0, this machine, marginal νSet check ×3):
**0.69 s vs 0.80 s** Id-form; `--profile=conversion` 3,133 compare
equal / 891 by reduction vs 3,271 / 952.  `frame4`'s normal form is
byte-identical to the Id-form tower's (zero transp/hcomp); all dimension
probes green.  The globular νGpd files (νGpd, νGpdBase, GpdLemmas)
and the P02 Σ≡-composition probes live on `globular`; the νGpd storey
on `main` is to be built fresh on the V4 + V2 base.


## νGpd storey closed on V4+V2 (2026-08-18..20)

`Bonak/νGpd.agda` is built and green: HGpd-valued frames / layers /
paintings (`gunit`/`gΣ`/`gΠ`), the mutual block grown by
coh2-frame / coh2-layer / coh2-painting, and exactly one truncation
site — `isGroupoid→Cube` inside coh2-layer, the cubical form of
Rocq's single GUIP use.  The s = 0 painting 2-coherence is
`cohLayer-fillP` (the filler of coh-layer's square composition),
exactly as the r = 0 painting coherence is `subst-filler` one storey
down.  Commit e9f5c38.

Closing coh2-layer's body hit three separate walls, each with its own
fix:

1. **Interval clause patterns trigger the boundary-confluence pass**,
   which simplify-normalizes and reifies the whole clause body per
   face on the success path.  Fix: the body is hoisted into
   `coh2-layer-suc` with λ-bound interval variables, typed against
   the folded instance type `Coh2LayerSucT` — instance-type folding,
   which Agda's mutual-block phasing forces anyway (a signature
   cannot apply a layer at an arity point before clauses exist).
2. **Kan operations in the tower's concrete Σ/Π fibers compute
   componentwise** with no sharing, exponentially in comp′ nesting
   via per-face context re-substitution; the pasting never finished
   at 35 GB.  Fix: the fused kit — the final section of
   `Bonak/GpdLemmas.agda`, a ~60-parameter anonymous module whose
   public lemma `coh2Layer-cubeP` states the entire four-lateral
   pasting (six `junctionP` cells, the `∙congF`/`∙Πapp` bridges —
   cong over ∙ is NOT definitional over abstract families — the
   stated laterals, `squarePOverCube`, and the base-pad transport)
   over abstract families, where every filler is neutral.
   coh2-layer's clause is a single application, mirroring coh-layer's
   `cohLayer-squareP`.  Analysis: `CONV-COST.md`.
3. **Agda's dead-code interface pass** costs ~90 s per filler
   parameter on the kit's telescope shape (76.9 s of a 77.9 s
   telescope-only run).  Local env-guarded patches
   (`AGDA_NO_DEADCODE`, `AGDA_CONV_CACHE`) made iteration workable;
   neither is needed to check νGpd itself.  Analysis and upstream
   plan: `DEADCODE-COST.md`.

Discipline notes that carry forward: family implicits applied at
composite terms are not Miller patterns and deadlock silently — every
kit application pins them (`{P = …}` etc.); interval-typed bindings
need explicit signatures (unannotated ones infer Π-over-I and leak
metas); where/module bodies do not allow forward references in types.

Measurements: νGpd alone re-checks in 2 m 27 s / 1.77 GB peak on
stock Agda 2.8.0 (deps cached), 3 m 02 s / 1.52 GB on the patched
binary; cold full build 53 m on stock (GpdLemmas' kit section
dominates: ~11 min of typing plus the interface pass);
GpdLemmas + νGpd rebuild under the patched binary 670 s / 10.5 GB.
νSet gate probes stay green.

Termination is now CHECKED (2026-08-20, later): the development
`{-# TERMINATING #-}` is removed and the block passes the termination
checker at `--termination-depth=4` — green at 4 (311 s / 1.6 GB
total, the analysis adds ~1–2 min over the type check) and at 5
(589 s — larger matrices), rejected at 3 on the
restr-frame..coh2-layer-suc group.  The boundary matches the dimension
discipline exactly: the coh2 statements write occurrences up to suc⁴
of the member's dimension, as νSet's suc³ statements need depth 3.

The `conv-cost` experiments concluded (2026-08-20, later) with a
corrected diagnosis: the kit's checking cost is per-binding section
overhead — every definition processed over the full ~60-parameter
telescope at ~5–9 s per binding regardless of content — and NOT the
pasting composites (flattening `junctionP` is perf-neutral; the
conversion cache is a wash).  The adopted fix is the staged
telescope: three nested anonymous modules binding parameters as late
as possible, each private binding in the innermost module it needs;
full-file check 766 → ~400 s (2×), lifted parameter order unchanged
so νGpd needed no edit.  Details and receipts: `CONV-COST.md`,
branch `conv-cost`.

The νGpd gate is in (2026-08-20, latest): `examples/ExamplesGpd.agda`
mirrors the νSet gate one storey up — νGpd at ⊤/Bool arity, the
level-5 point prefix of `gunit` fillers, and the compute gate
`frame5 = GDom (frame 5 5 0 tt pt5)`.  Marginal check 0.36 s / 42 MB;
`frame5` normalizes to a closed Σ/Π/⊤ nest with zero transp/hcomp —
the tower fully computes through the coh2 storey.

The DeadCode memoization prototype concluded (2026-08-20, latest)
with a clean negative: a StableName-keyed node memo over the
reachability fold, verified byte-identical on interfaces, hits 99.7%
and is still SLOWER than stock — instrumentation shows the lifted
signature is genuinely tree-sized (~89 K distinct nodes through
~33.5 M spine slots, sharing only at atoms), so there is no DAG for
a memo to exploit.  The pass is also untouched by the staged
telescope (2,428 s either way).

The DeadCode question CLOSED (2026-08-21): a second traversal-side
redesign (serializer-style interning, 99.87% hit rate) also landed
at parity — a forcing-only control bounds all discipline at ≤15% of
the pass — and the true seat of the cost was found: `goMeta` walks
every solved meta's judgement type, which with `--save-metas` off is
discarded before serialization anyway.  Skipping `jMetaType` under
that condition collapses the pass 164× (2,726 s → 16.6 s, module
total ~3,200 s → 428 s) with a byte-identical interface — the
upstreamable fix, replacing both the bypass and the "store less"
program for the default configuration.  Full data:
`DEADCODE-COST.md`.


## Mechanical νGpd cleanup on main (2026-09-25)

The successor type/helper are inlined with lambda-bound interval
arguments. The other coherence clauses use interval lambdas too.
The native composition proofs are retained. Of 178 named implicit
applications, 137 are removed; the retained hints include the painting
families and restriction functions, and `B`/`M` for the dependent Sigma
assembly. Unused aliases, eta-expansions, and two single-use arity
wrappers are removed. The remaining local aliases use `let` bindings.

All twelve core signatures are unchanged, and termination checks at
depth 3. Both example gates pass; explicit `frame5` normalization is
byte-identical to baseline. The source is 660 lines, down from 896.

With imported interfaces cached, νGpd checks in 7.80, 7.70, 7.90 s
(mean 7.80 s), versus 270.71 s before. Cold project builds of the
library and both example gates take 315.87 → 52.74 s. All runs are
sequential and memory-capped at 16 GiB; experimental probes are excluded.

These measurements use the unmodified installed Agda nightly 2.9.0.
The extra local-alias cleanup lowered the intermediate check from
22.31 s to 7.81 s. Broader family omission either leaves unsolved metas
or exceeds the bounded trial, so those inference hints are retained.

Detailed logs, compiler identity, source snapshots, inference experiments
and reproduction scripts are in this worktree’s `.work/REPORT.md`.


## Coherence argument inference (2026-09-25)

The cube assembly infers 46 previously explicit parameters. The Sigma
assembly infers its boundary paths while keeping both decomposition
components explicit: frame and layer squares for `Σ≡hex.hex`, layer
and painting squares for `Σ≡hex.Dep.hexᵈ`. The dependent assembly
infers its base square. On record-hcomp, the frame coherence pairs its
components directly. `∙Πapp` infers its two base paths. `BG` and the
existing family hints remain explicit. Local value bindings in
`coh2-layer` decrease from 80 to 36, with two expanded transports
replaced by the existing layer restrictions.

All twelve tower signatures are unchanged. Termination at depth 3,
both example gates, and byte-identical `frame5` normalization pass.
With unmodified nightly Agda 2.9.0, marginal νGpd means are
7.91 → 7.35 s (three samples each). Cold project builds,
including the library and both example gates but excluding probes,
take 59.73 → 58.78 s (one sample each). Baseline samples are retained
from the preceding comparison. External dependencies remain cached;
all runs are sequential under a 16 GiB cap.

Sources, compiler identity, individual timings, inference trials and
reproduction scripts are retained in `.work/REPORT.md` in the
`coherence-argument-inference` worktree. The earlier
one-component API measurements are preserved separately there.


## Interval operator fixities (2026-09-25)

Agda removed the fixity declarations for its named cubical primitives in
[commit 9f2e184](https://github.com/agda/agda/commit/9f2e1843e6ca266a694e3681a8d64c1975249ae4).
Renaming those primitives without explicit fixities leaves both `∨`
and `~` at precedence 20, so `i ∨ ~ j` no longer parses. Prelude now
assigns `infixr 20` to `∧` and `∨`, and `infix 30` to `~`, in the
renaming clause. These are the fixities the older compiler supplied.

`make install` successfully installed nightly source revision
`9c1bd18a31ae1f5168055735424aa2881e7747ca`. With that compiler, an isolated
probe reproduces the original parse error. After the fix, `make clean`
followed by `make build` checks both example roots and their dependencies
in 64.38 s, with a peak RSS of 7,703,152 KiB, under a 16 GiB cap.
Project interfaces were cold. Installation and verification logs, the
compiler identity, and source archive metadata are retained in
`.work/nightly-update/` in the `make-build` worktree.
