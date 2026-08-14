# V4 (fillers-only storage + `(p,k)` indexing) — build report

Worktree `/home/olympichek/bonak/cubical-bonak/fillers-only`, branch
`fillers-only`, Agda 2.8.0 (optimise-heavily), 2026-08-14.

**Canonicalized (same day, later):** variant (b) is the canonical
`Bonak/νSet.agda` of this branch (gate: `probes/Examples.agda`);
variant (a) and the V1 mirror's `νSet.agda`/`Examples.agda` are removed
here (V1 lives on `main`). File names below are the build-time ones;
the measurements are unaffected.

**Result: V4 builds, computes, and is 8× cheaper than V1 to typecheck.**
The two claimed savings (no zipper, no inequality layer) both
materialize, at zero conversion cost — the V1 hotspot has no analogue in
V4 rather than a cheaper one. Two prices: one rewrite rule pair on `ℕ`
addition, and six of eleven members carrying `{-# TERMINATING #-}`.

## Artifacts

| file | what |
|---|---|
| `Bonak/NatRew.agda` | 49 l — `+-zero`, `+-suc` as REWRITE rules |
|  `Bonak/νSetV4.agda` (removed) | 291 l (≈205 code) — the full tower, prefix = `Σ` (variant a) |
|  `Bonak/νSetV4R.agda` (now `Bonak/νSet.agda`) | 309 l — same, prefix = no-eta record (variant b) |
| `probes/ExamplesV4.agda` (removed), `probes/ExamplesV4R.agda` (now `probes/Examples.agda`) | the gates |
| `probes/V4-P00-rewrite.agda` | the decisive first probe (below) |

All eleven members are present and closed: `Pre`, `Fil`, `frame`,
`layer`, `painting`, `restr-{frame,layer,painting}`,
`coh-{frame,layer,painting}`, plus the coinductive `νSet→`. No
postulates, no admits, no holes. `Bonak/{Prelude,LeProp,RewLemmas}.agda`
are used unchanged — `LeProp` in particular is byte-identical to V1's.

## 1. Probe: the `(p,k)` prefix-length obstruction, and the rewrite rules

The probe the review asked for first was the eta question. It turned out
that a *prior* question decides the design, so that one came first.

`frame p k D` needs a prefix of `p + k` fillers, and the tower moves both
indices: `frame` steps `(suc p, k) → (p, suc k)`, `painting` steps the
other way, `layer` peels the top filler. So the prefix former must
satisfy all three of

```
p + zero  ≡ p            -- painting's base: at k = 0 the frame index IS
                         -- the prefix length, so the stored filler
                         -- applies with no coercion (this is exactly
                         -- Alice's `recover-nat-eq`, made definitional)
p + suc k ≡ suc (p + k)  -- peeling the top filler
suc p + k ≡ suc (p + k)  -- re-splitting the same prefix
```

and **no orientation of a recursive addition gives all three**, because a
defined function reduces on one scrutinee at a time. This is the
reversal obstruction of the proposal, in its Agda form: it is a
definitional-equality fact, so a different representation cannot dodge
it. Checked and rejected before settling: a two-index `I p k` recursive
on `k` (re-split not definitional), recursive on `p` (top peel not
definitional), a split Root/Tail zipper (one of "peel the top" and "move
the marker" is always O(k) and stuck under a variable `k` — the
`SINGLE-BLOCK-REPORT` staircase, reproduced), an inductive family (a
length-n prefix would need two output indices, or induction-induction
which Agda does not have), and carrying `n` as an independent third index
(then `p ≡ n` at `k = 0` is not definitional and `recover-nat-eq` comes
back).

`probes/V4-P00-rewrite.agda` tests the way out. Gates, all green:

- `--cubical --prop --guardedness --rewriting` coexist;
- the **cubical Path type is accepted as the REWRITE relation** (no
  inductive `Id` needed);
- with `+-zero` and `+-suc` declared as rewrite rules all four addition
  equations hold definitionally **at variable `p` and `k`**, including in
  type position (`Pre (suc p + k) ≡ Pre (p + suc k)` by `refl`);
- `LeProp` is untouched: `suc q ≤ suc k` still reduces to `q ≤ k`, so a
  bound is passed one level down verbatim.

So `I p k` is just `Pre (p + k)`, a plain snoc list of fillers, and the
"split filler-prefix family" of review item 6 does not need to exist.
Caveat recorded in `NatRew.agda`: Agda's confluence checker does not
support `--cubical` (it warns and skips); asking for it anyway reports
the `+-zero`/builtin-clause overlap as a failure because it does not
apply the rule under scrutiny while checking it. The critical pairs join
by hand (`suc n + 0` ⇒ `suc n` one way, `suc (n + 0)` ⇒ `suc n` the
other), and both rules are proved lemmas, so nothing is assumed — but the
conversion relation is extended, and that has no Rocq analogue.

## 2. The D-typing / descent decision

**Decision: `I p k := Pre (p + k)` with the two rewrite rules; the prefix
is one snoc list, never split.**

**No reified descent of any kind was needed** — no `GChain`, no CPS, no
stored-top-plus-step. Direct structural recursion inside the mutual
block suffices. The reason is worth recording, because it is the reason
`projSteps` never appears: the tower never relates `I (j + p) k` with
`I p (j + k)` for a *variable* `j`. Every descent it performs is one
level (`layer` at dimension `p+k+1` consuming `painting` at `p+k`), and
one level is `Pre (suc n) = Σ (Pre n) (Fil n 0)` — a single peel, which
the rewrite rules make available in either split. The `j`-step chain
that Rocq had to reify was an artifact of relating *stored strata* across
stages; with nothing stored, there are no stages to relate.

Correspondingly, **no stage-commutation glue was proved or needed**, and
none was transported through the block. The V1 profile's 98% —
`mkExtraCohs`' π₁-commutations, `mkExtraCohs (AddCoh2Dep …) ≡ AddCohDep
…`, `fst (mkRestrPaintings …) ≡ Prefix …` — has no V4 analogue: those
are facts about the four `Deps*` image maps, and V4 has no image maps.
Risk 4 of the proposal ("the successor of the actual V1 hotspot") does
not materialize; the hotspot is deleted rather than replaced.

Two definitional facts the construction leans on, both holding by clause
unfolding, neither needing a lemma:

- the bottom-index case, `restr-painting p k D E 0 tt ε d (l , c) = l ε`,
  reduces at *variable* `p`, `k` and a variable prefix, because layers
  are functions and `nth` is application (V1 decision 1). This is the
  hazard the brief flagged; layers-as-functions is what disarms it.
- V1 decision 9's byte-identity discipline becomes automatic:
  `coh-frame (suc p) …` literally unfolds to
  `Σ≡ (coh-frame p …) (coh-layer p …)`, which is exactly what `Σ≡dep`
  consumes in `coh-painting`. There is no stored term to keep aligned
  because there is no store.

## 3. Numbers

Marginal check time, dependencies cached, three runs each, and total
`compare` count from `--profile=conversion`:

| | lines | check (s) | conversions |
|---|---|---|---|
| V1 `νSet.agda` (this machine, today) | 621 | 6.54 / 6.14 / 6.22 | 37,907 |
| **V4 (a), `Σ` prefix** | **291** | **0.74 / 0.76 / 0.82** | **4,820** |
| **V4 (b), no-eta record prefix** | **309** | **0.47 / 0.37 / 0.46** | **3,859** |

Cold full check including `Prelude`/`LeProp`/`RewLemmas`/`NatRew` and the
gate file: V1 5.9–7.5 s, V4 (a) 1.2–1.6 s, V4 (b) 1.0 s (the spread is
run-to-run noise on this machine).

Reference points from `PORTING-NOTES.md`, not re-measured here: V1 with
eta 310 s / 6.19M conversions, post-eta-fix 5.1 s / 38k; V2 (PathP)
3.9 s; V3 (rew) 5.8 s; Rocq `νSet.v` 1.85 s. Today's V1 number (6.2 s,
37.9k) reproduces the recorded post-eta-fix figure, so the comparison is
like-for-like.

**V4 is ~8× faster than V1 and needs ~8× fewer conversions.** It is
~5× faster than V2, the cheapest of the three equality variants, on an
axis orthogonal to V2's — and V2's saving (PathP-native equalities) is
still available on top.

### The eta axis (probe 1 proper)

Σ has definitional eta and no off switch, so variant (b) makes the prefix
a per-level `no-eta-equality; pattern` record — the only record the
construction still contains.

- The blowup does **not** reappear on the prefix. Variant (a)'s
  eta-expanding record comparisons: 208, against V1's 393 and the
  6.19M-conversion disaster's cause. There is no combinatorial tower of
  record η left to expand, because the fields the tower projects are one
  prefix and one filler, not four dependent `Deps` bundles.
- Variant (b) is nonetheless the cheaper of the two: 3,859 vs 4,820
  conversions, 0.43 s vs 0.77 s, and eta-expansions drop 208 → 30. So
  the eta lever survives fillers-only storage and is still worth pulling,
  but it now buys ~1.8× rather than ~60×.
- Variant (b) has a real cost, and it is exactly the documented hazard:
  without eta a clause only fires on a constructor, so the `r = 0`
  reduction `restr-painting … 0 ↦ l ω` forces `coh-painting`'s `r = 0`
  clause to *match* the prefix even though its proof (`refl`) never uses
  it. Miss that and the clause fails to typecheck. Variant (b) also
  needs one more `{-# TERMINATING #-}` than (a).

### Sharing / recomputation axis

The review's added axis — stored `Deps*` memoize strata, fillers-only
recomputes — shows no penalty at this dimension: recomputing
`frame`/`painting` as function applications is *cheaper* here than
carrying and comparing the memo. agda-alice being the slowest artifact
ever measured is therefore not attributable to fillers-only storage; on
this evidence it is attributable to her `Inequalities.agda` layer, which
V4 does not have.

## 4. Gate

`probes/ExamplesV4.agda` mirrors `Bonak/Examples.agda`:
`AugmentedSemiSimplicial`, `SemiSimplicial`, `SemiCubical`, and
`SemiSimplicial4 = Pre 4` (V1's `prefix (νSetAt 4)` *is* the list of four
fillers, which fillers-only storage calls `Pre 4`), plus an inhabitant
`pt4 : Pre 4` and `frame4 = Dom (frame 4 0 pt4)`.

- `frame4` normalizes to a **fully computed** nested Σ/Π of `⊤` — 0
  occurrences of `transp`/`hcomp`. Variants (a) and (b) produce
  character-identical normal forms.
- `SemiSimplicial4` normalizes to 45,935 characters against V1's 46,778,
  with **195 `transp`/`hcomp` occurrences in each**. The V1 "probe G3
  wart" is thus reproduced exactly, neither better nor worse: the residue
  is on the equality-representation axis (V2/V3), not the storage axis.
  Empirical confirmation of the proposal's orthogonality claim.
- Under (b) the prefix type itself no longer flattens (558 chars), the
  expected consequence of a record without eta; the compute gate
  `frame4` is unaffected.

## 5. The one thing that did not close: termination

`--termination-depth=2` was tried first as the review predicted, then
3, 4, 5 and 6. **All fail.** Six of the eleven members —
`frame`, `layer`, `painting`, `restr-frame`, `restr-layer`,
`coh-frame` — carry `{-# TERMINATING #-}`, in both variants. (Stripped
of all pragmas, variant (b)'s rejected set is larger by two and smaller
by one: no eta means less structural information for the checker. With
the six above in place both variants are green.)

This is a checker-strength problem, not a soundness one: every cycle in
the block either shrinks the prefix or decreases `p` or `k`. What the
size-change analysis cannot see is the shrinking one, and the reason is
structural to V4 rather than incidental — **the quantity that decreases
is the prefix's length, which under `(p,k)` indexing is `p + k`, an
expression appearing in types and an argument of nothing.** Alice's
absolutely-indexed block passes exactly because that level is her first
argument. This is the indexing discipline's one real bill, and it is
payable in a pragma.

What was measured on the way, in case it is resumed:

- Argument *column* alignment is load-bearing (the checker compares
  caller and callee arguments by position). Moving the prefix to a fixed
  column in all eleven members and matching it (`(D , E)`) rather than
  projecting it (`fst D`) is what shrinks the rejected set to six; the
  reading order `p k q r … D d` is rejected outright.
- A `where` block in `coh-layer` *loses* termination information: Agda
  lifts the bindings to top level with all clause variables as
  parameters, so the prefix argument becomes a function call and its
  constructor structure disappears. Inlining the abbreviations restores
  it. (`coh-layer`'s body is therefore written out in full.)
- Removing any single one of `restr-layer`'s four calls makes the block
  pass. Doing that properly — abstracting `restr-layer` over its `r = 0`
  frame coherence, which is V1 decision 3's fix for the same problem —
  was implemented and does move `painting`, `restr-layer` and
  `restr-painting` across, leaving six others. It costs four extra
  explicit coherence arguments in `coh-layer`'s statement, so it is not
  in the committed file; the diff is reconstructible from this note.

## 6. Other frictions worth recording

- **Definition order inside the mutual block.** `Pre` and `Fil` must be
  *defined* immediately after being declared: later signatures project
  out of a prefix, and a merely declared function does not reduce. Alice
  does the same; it is not optional.
- **Implicits (V1 decision 8, at larger scale).** In `coh-layer`, all
  twelve of `rew-cohLayer33`'s point and path implicits
  (`E1 m1 m2 C1 C2 n1 n2 D1 D2 K aL aR`) must be given explicitly, not
  just the eight type-level ones V1 supplied. The goal only exposes them
  after unfolding two nested `restr-layer` clauses, and the unifier gives
  up there. Once given, the proof is V1's verbatim: `Π-subst-ext`, then
  `rew-cohLayer33` with the painting coherence and `isSetDom` (the
  coh2-frame, free because frames are HSets — V1 decision 7 carries over
  untouched).
- **The `(p,k)` payoff is visible in the source.** Bounds are passed to
  the next level with no adjustment at all (`Hq : q ≤ k` is literally the
  proof of `suc q ≤ suc k`); there is no `recover-nat-eq`, no `₂/₃/₄`
  records, no stored differences, no `drop₃`/`drop₄`, no `⇑`/`⇓`.
  `LeProp.agda` stays at 65 lines against agda-alice's 192-line
  `Inequalities.agda`, and V4's tower is ~205 lines of code
  (291 with its header) against her 315, and V1's 621.

## Verdict

V4 delivers what it promised, and the conversion cost is not merely
acceptable — it is the lowest of any variant built so far. Fillers-only
storage removes the zipper by removing the things it maps between, and
the removal takes the actual V1 hotspot (98% of check time in
π₁-commutations) with it rather than replacing it with an analogue;
`(p,k)` removes the inequality layer, and its bounds compose for free
because `suc q ≤ suc k` reduces. Neither half needed the other's
predicted rescue: no chain reification, no CPS, no stored-top, no
propositional glue anywhere in the block. The two bills are real but
small and clearly localized: the prefix's length forces two rewrite rules
on `ℕ` addition (a genuine extension of definitional equality, with no
Rocq analogue and an unchecked confluence caveat under `--cubical`), and
that same length — being a type-level expression rather than an argument
— is invisible to the termination checker, costing six
`{-# TERMINATING #-}` pragmas on definitions that still compute. On the
evidence here the recommendation is to carry V4 forward as the storage
discipline for the νGpd storey and to combine it with V2's PathP-native
equalities, whose saving is on an orthogonal axis and, per the identical
195-residue counts, still entirely on the table.
