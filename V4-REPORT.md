# V4 (fillers-only storage + `(p,k)` indexing) — build report

Worktree `/home/olympichek/bonak/cubical-bonak/fillers-only`, branch
`fillers-only`, Agda 2.8.0 (optimise-heavily), 2026-08-14.

**Canonicalized (same day, later):** variant (b) is the canonical
`Bonak/νSet.agda` of this branch (gate: `probes/Examples.agda`);
variant (a) and the V1 mirror's `νSet.agda`/`Examples.agda` are removed
here (V1 lives on `main`). File names below are the build-time ones;
the measurements are unaffected.

**Canonicalized again (2026-08-17, later):** the fuel tower is now the
canonical `Bonak/νSet.agda` of this branch — `Bonak/νSetF.agda` and its
gate `probes/ExamplesF.agda` are renamed to `Bonak/νSet.agda` and
`probes/Examples.agda`, and the 1-pragma tower they sat beside is
removed. The output-fuel section's side-by-side comparison below keeps
the pre-rename names.

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

---

## Termination revisited (2026-08-15)

**Goal: zero `{-# TERMINATING #-}`. Not reached.** The file now carries
**one** pragma instead of six, the rejected cycle is identified edge by
edge, and the abstraction route §5 recommended is refuted by
measurement. Everything below is measured on this machine, Agda 2.8.0.

### 1. The pragma count was never six

`{-# TERMINATING #-}` is attached to the **mutual block**, not to the
definition it precedes. One occurrence switches the check off for all
eleven members; the six in the committed file were five redundant ones.
Verified directly (`f n = g n; g n = f (suc n)` with a pragma on `f`
only is accepted), and by pragma'ing each member of the block alone —
every single one makes the whole file green. So "six of eleven members
carry a pragma" in §5 overstates the bill: the bill is *one pragma for
the block*, which is also the least any variant of this block can carry.

`Bonak/νSet.agda` now carries exactly one, on `frame`, with the analysis
in the header comment.

### 2. The rejected cycle

Stripped of pragmas the checker rejects
`{frame, layer, restr-frame, restr-layer, coh-frame, coh-layer,
coh-painting}` — `painting` and `restr-painting` pass — and lists ten
problematic calls. They form **one loop**:

| # | edge | call site | Δp | Δk | Δprefix |
|---|---|---|---|---|---|
| 1 | `frame → frame` | `frame (suc p) k D = hΣ (frame p (suc k) D) …` | +1 | −1 | 0 |
| 2 | `frame → layer` | same clause, `λ d → layer p k D d` | +1 | 0 | 0 |
| 3 | `layer → restr-frame` | `layer p k (D ∷ E) d`, the `0`-restriction | 0 | 0 | 0 |
| 4 | `restr-frame → restr-layer` | `restr-frame (suc p) k D … (d , l)`, 2nd component | +1 | 0 | 0 |
| 5 | `restr-layer → coh-frame` | the `subst`'s `r = 0` frame coherence | 0 | 0 | 0 |
| 6 | `coh-frame → coh-layer` | `coh-frame (suc p) k D …`, `Σ≡`'s 2nd argument | +1 | 0 | 0 |
| 7 | `coh-layer → coh-painting` | `rew-cohLayer33`'s painting-coherence premise | 0 | 0 | +1 |
| 8 | `coh-painting → coh-painting` | `coh-painting (suc p) k …` | −1 | +1 | 0 |
| 9 | `coh-painting → coh-layer` | `Σ≡dep`'s 2nd argument | 0 | +1 | 0 |
| 10 | `coh-layer → frame` | `isSetDom (frame p k D)` — the free 2-dim. frame coherence | 0 | 0 | +3 |

Summed around the loop this is Δp = +3, Δk = +1, Δprefix = +4: on
paper all three columns decrease, and the checker still rejects it.
That gap — not the p + k point of §5 — is the thing to explain, and §4
below isolates it.

**Deleting any single one of the ten makes the whole block pass**, at
`--termination-depth` 1, 2, 3, 4, 5, 6, 8 and 10 alike (§5 tried 2..6;
depth is simply not the axis). §5's "removing any single one of
`restr-layer`'s four calls makes the block pass" is the special case #5
of this. Re-measured, the other three do not behave that way: deleting
`restr-layer`'s `restr-painting` call leaves the same seven members
rejected, and deleting its `painting` or `restr-frame` call stops the
file typechecking, so those two were never actually put to the checker.

Each of the ten is a defining clause of the tower — `frame`'s Σ,
`layer`'s Π, `painting`'s Σ, `restr-frame`'s pair, `restr-layer`'s
`subst`, `coh-frame`'s `Σ≡`, `coh-painting`'s `Σ≡dep` — except #10,
which is the isSet premise that is free because frames are HSets.

### 3. Why the "prev trick" does not sever it

The brief's plan was V1 decision 3: abstract the offending call out of
the block as an explicit argument, supplied one level up. Abstraction
does not *delete* an edge, it *moves* it to the caller — and on this
loop every caller is on the loop. Three abstractions were modelled and
all three leave the verdict unchanged:

- `restr-layer` abstracted over its `r = 0` frame coherence (edge #5,
  §5's own proposal): the call moves to `restr-frame` (Δp = +1) and to
  `restr-painting` (Δk = +1) — both already on or feeding the loop.
- `layer` abstracted over its `0`-restriction (edge #3): the call moves
  to `frame`, edge #2's caller.
- `coh-layer` abstracted over the isSet premise (edge #10, the only
  non-structural edge): the call moves to `coh-frame` (Δp = +1) and
  `coh-painting` (Δk = +1), edges #6 and #9's sources.

So the clique cannot be severed by abstraction: the loop's ten edges are
the tower's own definition, and its callers are its members.

### 4. What the checker actually loses (two mechanisms, both eliminated, verdict unchanged)

Two things weaken the analysis here beyond the p + k point of §5. Both
were removed experimentally; neither is sufficient.

**(a) The `pre` / `fil` projections in the result types.** They do not
stay in the types. `restr-frame`'s target `Dom (frame p k (pre D))`,
`restr-layer`'s `Dom (layer p k (pre D) …)` and the coherence statements
reappear *inside the clause bodies* as the solved implicit arguments of
`_,_`, `subst`, `Σ≡` and `Σ≡dep` — Agda's error even points at the
signature line for calls it found in a body. A projected prefix is
opaque to the structural order, so those calls contribute "unknown" in
the very column the measure lives in.

A rewrite eliminating them was implemented and typechecks: every member
takes the prefix already **split** into its base `D : Pre (p + k)` and
one explicit filler per level of look-ahead (`layer p k D E`,
`restr-layer p k D E₁ E₂`, `coh-layer p k D E₁ E₂ E₃`, …), so `pre` and
`fil` never occur, and column 3 has length exactly `p + k` in every
member — i.e. the measure §5 called invisible becomes the structural
size of a fixed column. Cost/benefit measured: 3,507 conversions
(−9 %) but 0.50 s marginal (+30 %), and — the reason it is not kept —
`frame (suc p) k D` stops reducing at a *variable* prefix, because the
peel moves into `frame`'s own clause. `Pre 4`'s normal form changes
accordingly. Verdict: **still rejected, same seven members**.

**(b) `Pre` being a type defined by recursion on ℕ rather than an
inductive family.** New probe `probes/V4-P01-termination.agda` isolates
this. `FunPre` is the loop of §2 and nothing else — seven members, ten
calls, same columns, same index discipline, same no-eta prefix, results
erased to `Box` — and it reproduces the rejection exactly, member for
member. `IndPre` is the same ten calls with `Pre` a length-indexed
inductive family (induction-recursion with `Fil`), and it is
**accepted, with no pragma**. So the checker can follow this cycle when
the prefix's length is a constructor index it can read, and cannot when
the length only appears as the argument of a recursive type former.

Combining (a) and (b) on the real file — split prefix *and*
`data Pre : ℕ → Set₁` with `⟨⟩`/`_∷_` — typechecks, is positivity-clean,
and is **still rejected**: the full block has edges the ten-call model
does not, notably more implicit-borne calls out of `restr-layer`'s
`subst` and `coh-layer`'s `Π-subst-ext` / `rew-cohLayer33`. It also
costs four `UnsupportedIndexedMatch` warnings (matching `Pre (suc n)`
needs `suc`-injectivity, which Cubical Agda does not support) and
changes `Pre 4`'s normal form. Not kept.

### 5. One correction to §5

> A `where` block in `coh-layer` *loses* termination information …
> (`coh-layer`'s body is therefore written out in full.)

Not reproducible, and the committed file contradicts it: `coh-layer`
**does** have a `where` block (`P₁ P₂ P₃ H₁ H₂ dR dE b`). Inlining it in
full changes the printed call terms (the lifted `Bonak.νSet.P₂ p k D …`
applications become the constructor terms) but leaves the rejected set
and the problematic-call list byte-for-byte equivalent. The `where` is
kept, for readability.

### 6. Numbers and gates

| | committed | now |
|---|---|---|
| pragmas | 6 | **1** |
| marginal check of `Bonak/νSet.agda` | 0.37 / 0.39 / 0.85 s | 0.38 / 0.38 / 0.38 s |
| conversions (`--profile=conversion`) | 3,859 | **3,859** |
| cold full check incl. the gate | 1.11 s | 0.83 / 0.88 / 0.89 s |

`probes/Examples.agda` green. `frame4` and `SemiSimplicial4` normal
forms **byte-identical** to the committed state (captured through
`agda --interaction`, `Cmd_compute_toplevel`); `frame4` still has zero
`transp`/`hcomp`. The `q = 0` / `r = 0` bottom-index reductions at
variable prefixes are untouched — nothing in the shipped diff touches a
clause. `probes/V4-P01-termination.agda` is green (its `FunPre` carries
the pragma; remove it to reproduce the rejection).

### 7. Trust posture

Two meta-obligations, unchanged in kind and one smaller in size:

1. **The REWRITE confluence hand-check** (`Bonak/NatRew.agda`): Agda's
   confluence checker does not support `--cubical`, the two rules are
   proved lemmas, and their one critical pair joins by hand. This
   remains the file's genuine extension of definitional equality.
2. **One `{-# TERMINATING #-}` on the mutual block.** The recursion is
   well-founded — every cycle either shrinks the prefix or decreases p
   or k — and §2 says exactly which loop the size-change analysis cannot
   follow and §3 why no abstraction available inside this design severs
   it. The pragma is a checker-strength concession, not a soundness one;
   the definitions still reduce and the compute gate passes.

The honest summary of the storage-discipline experiment is therefore
unchanged from the Verdict above, with one bill re-costed: fillers-only
+ (p,k) buys an 8× conversion saving for two rewrite rules and *one*
unchecked termination pragma — not six.

---

## The fuel column (2026-08-15): attempted, refuted

**Goal: replace the pragma by an explicit fuel argument, per the recipe
of `probes/V4-P02-fuel.agda`. Not reached.** Two complete variants of
the block were built and typecheck; each is rejected by the termination
checker, for opposite reasons, and the reasons combine into an
obstruction that no single fuel column can avoid. The file is back to
its one-pragma state, byte-for-byte. Measured on this machine,
Agda 2.8.0.

### 1. What the port needs before it can even be written

- **A definitional equation on ℕ.** The probe carries the fuel with
  `e : n ≡ p + k` and peels it with `injSuc`. At scale that is unusable:
  `injSuc e` is a term, it appears in the types of every member, and two
  peels of the same equation are not syntactically equal, so the
  statements stop matching up. The replacement is a recursive equality
  mirroring `Bonak.LeProp`'s `≤`:

  ```
  EqN zero zero = ⊤ ; EqN zero (suc m) = ⊥ ;
  EqN (suc n) zero = ⊥ ; EqN (suc n) (suc m) = EqN n m
  ```

  `EqN (suc n) (suc m)` *reduces* to `EqN n m`, so peeling is the
  identity on proofs; `EqN zero (suc m)` is `⊥`, so the impossible
  clauses close with an absurd pattern; and passing it irrelevantly
  (`.(e : EqN n …)`, as the `q ≤ k` bounds already are) gives
  definitional proof irrelevance, so no proof term ever has to be
  matched with another. With it the port is transport-free.
- **A fuel-polymorphic filler.** `Fil p k D` becomes
  `(m : ℕ) .(f : EqN m (p + k)) → Dom (frame m p k f D) → HSet₀`: a
  stored filler eats a point at any fuel, which is what lets
  `painting p 0 D E d = E _ _ d` still fire when the point's fuel is a
  variable. Without it the k = 0 clause does not typecheck.

### 2. Two variants, two rejections

**(a) Fuel = the member's index sum `p + k`.** Every frame / layer /
painting occurrence in a type carries the fuel of its own dimension,
written `n`, `suc n`, `suc (suc n)`, `suc (suc (suc n))`. The block
typechecks. Rejected: `restr-frame`, `restr-layer`, `coh-frame`,
`coh-layer`, `coh-painting`. Cause: a member's *statement* mentions
members at a HIGHER dimension — its own point and layer arguments live
over the full prefix — so those statement-borne calls (which the checker
counts, as they reappear as solved implicits in the bodies) *increase*
the column, e.g. `coh-frame` at fuel `n` mentions
`restr-frame (suc (suc n)) …`.

**(b) Fuel = the length of the member's own prefix.** Now every
statement occurrence points downward or stays level, and the three
coherences pass. Rejected: `frame`, `layer`, `restr-frame`,
`restr-layer`, `restr-painting`. Cause: a signature has no way to name
"one less than my fuel" except `predℕ n`, and **the termination checker
does not reduce `predℕ (suc n)`** — three-line probe, rejected:

```
f (suc n) = g (predℕ (suc n))
g n       = f n
```

So `restr-frame`'s result type `Dom (frame (predℕ n) p k _ (pre D))`
contributes an unknown entry in the very column the measure lives in.

### 3. Why no single column of this shape can work

Give every application a level, and write it as `|prefix| + c_M` with a
constant per member. Two forces act on it:

- *expressibility*: a signature can only write `suc^j` of its own fuel
  variable, so every application named in a member's statement must have
  level ≥ that member's;
- *the checker*: every call, statement-borne ones included, must have
  level ≤ its caller's.

Together they force every statement occurrence to sit at exactly the
member's level. Solving those equalities across the nine members makes
all the `c_M` equal, i.e. level = `p + const` — and `p` increases on
`coh-painting`'s p↔k trading clause. Hence no level of that shape is
both expressible and non-increasing. The `frame → frame` edge pins the
rest: `layer`'s point argument has to be typed
`Dom (frame <layer's own fuel> …)` for that edge to keep a known column,
so the fuel cannot be kept out of the types, which is exactly what the
probe's model avoids by erasing all results to `Box`.

### 4. The route not taken

Give every restriction and coherence an **output fuel**, universally
quantified as `Fil` already has one. Then a peel is free — the caller
instantiates the output fuel with a pattern-derived value, so no
`predℕ` and no unknown entries — and the loop's descent
(`coh-layer → coh-painting`, where the premise comes from a layer's Π
and therefore lives one fuel below) becomes visible. It fragments
quickly: the two sides of the frame coherence restrict through different
intermediate objects, so `coh-frame` needs two intermediate output fuels
and the layer and painting coherences inherit them, putting 4–6 extra
arguments on every coherence statement. Not attempted here.

### 5. State and numbers after the attempt

`Bonak/νSet.agda` and `Bonak/NatRew.agda` are back to their pre-attempt
content; `probes/V4-P02-fuel.agda` is unchanged and still green.

| | before the attempt | after |
|---|---|---|
| pragmas in the block | 1 | 1 |
| marginal check of `Bonak/νSet.agda` | 0.44 / 0.44 / 0.43 s | 0.38 / 0.42 / 0.39 s |
| conversions (`--profile=conversion`) | 3,859 | 3,859 |
| cold full check incl. the gate | 0.93 s | 0.90 s |

`probes/Examples.agda` green; `frame4` and `SemiSimplicial4` normal
forms (captured through `agda --interaction`, `Cmd_compute_toplevel`)
byte-identical to the captures taken before the attempt — 485 and 466
characters, character for character. The trust posture of the previous
section is unchanged: two rewrite rules whose confluence is hand-checked,
and one termination pragma on the mutual block.

---

## The output fuel route (2026-08-17): the pragma falls

**Goal: implement §4 of the previous section — output fuels on the
restrictions and coherences — and reach zero `{-# TERMINATING #-}`.
Reached, though not by the sketched design.** The sketch's free output
fuels are refuted by definitional equality; what conversion forces
instead is exactly variant (a) of the fuel attempt, and variant (a)'s
rejection turns out to be a `--termination-depth` artifact.
`Bonak/νSetF.agda` is the resulting tower: fuel columns, no pragma, no
postulates, accepted at `--termination-depth ≥ 3`, and its `frame4`
normal form is byte-identical to `Bonak/νSet.agda`'s. Everything below
is measured on this machine, Agda 2.8.0.

### 1. Free output fuels are unusable (probes/V4-P03-output-fuel.agda)

The sketch was: a restriction takes its result's fuel `m` as a fresh
universally quantified argument, so no signature ever writes `predℕ`,
and the caller instantiates `m` with a pattern-derived value. Two
walls, both mechanical consequences of one fact — **a layer's
components only reduce at a constructor-form fuel, and the reduction
pins them to the pattern fuel**:

- `restr-painting`'s q = 0 clause is `l ε`, and `l`'s Π-type only
  fires after matching the input fuel as `suc n₀`, producing a
  painting at fuel `n₀` where the signature promises fuel `m`.
  Rejected: `n₀ != m of type ℕ`. The two are propositionally equal
  (both `EqN`-related to `p + k`) but a cast between them is exactly
  the recursive fuel coercion this design exists to avoid.
- `restr-layer`'s result `Dom (layer m …)` is stuck at the free `m`,
  so its clause cannot even take the arity argument:
  `Cannot eliminate type … with variable pattern ω`.

So the output's fuel must be the member's *own* variable with the
input written `suc` of it — and then the two intermediate fuels §4
expected `coh-frame` to need are forced equal (the outer restriction's
input IS the inner's output), and the whole discipline collapses into
variant (a): one fuel per member, every occurrence written `suc^j` of
it. The bill is two extra arguments per member — the fuel and one
irrelevant `EqN` proof — not §4's four-to-six: since
`EqN (suc n) (suc m)` reduces to `EqN n m`, the single proof a member
holds types every occurrence verbatim, at any depth.

### 2. Variant (a)'s rejection was a depth artifact (probes/V4-P04-depth.agda)

Variant (a) was rejected because statement-borne calls carry fuels
above the caller's own — by up to three constructors (`coh-layer`'s
point is a `frame` at `suc³` of its fuel). Those are *bounded*
increases, and bounded increases are precisely what
`--termination-depth` exists for; the fuel attempt ran at the file's
depth 2 and the depth sweep of the pragma section was only ever run on
the fuel-less file. The probe settles it: V4-P02's ACCEPTED `FuelPre`
model plus one explicit call per statement-borne occurrence of the
variant-(a) signatures, at its real offset, is rejected at depths
1–3 and **accepted at depth 4**, no pragma.

### 3. The tower: Bonak/νSetF.agda

The port (with `Bonak/EqProp.agda` supplying `EqN`, mirroring
`LeProp`):

- every member takes `(n : ℕ)` first plus one irrelevant
  `.(e : EqN n <base dimension>)`; the base dimension is the member's
  lowest-dimensional occurrence (`p + k` for frame / painting /
  restr-frame / restr-painting / coh-frame / coh-painting,
  `suc (p + k)` for layer / restr-layer / coh-layer);
- `Fil` is the one fuel-polymorphic spot:
  `Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → Dom (frame m p k f D) →
  HSet₀`, which is what lets `painting`'s base case apply a stored
  filler at the variable fuel a peel produces;
- fuel is matched in exactly three places — `layer`, `restr-layer`,
  `coh-layer` peel one `suc` in step with the prefix — adding three
  absurd clauses (`EqN zero (suc _)` is ⊥); everything else receives
  its fuel as a determined term;
- the clause bodies are Bonak.νSet's with fuels filled in by
  dimension, `coh-layer`'s `rew-cohLayer33` paste included; the
  discipline is rigid enough that the only porting error made (a fuel
  one `suc` short on `coh-layer`'s `dR`/`dE`) was caught by the type
  checker.

**Accepted with no pragma at `--termination-depth = 3`** (rejected at
2; the file pins 3 in its OPTIONS). The depth flag bounds the
constructor-depth the checker's call-matrix composition tracks; it is
a search knob, not an assumption.

### 4. Gates and numbers

| | `νSet.agda` (1 pragma) | `νSetF.agda` (0 pragmas) |
|---|---|---|
| marginal check, 3 runs | 0.33 / 0.33 / 0.33 s | 0.81 / 0.81 / 0.81 s |
| `--profile=conversion` compare equal | 2,648 | 3,271 |
| compare by reduction | 795 | 952 |
| cold check incl. its gate | 0.74 s | 1.21 s |

`probes/ExamplesF.agda` green (fillers written `λ m f d → …`).
`frame4`'s normal form (captured through `agda --interaction`,
`Cmd_compute_toplevel`) is **byte-identical** across the two towers —
at closed dimensions every fuel reduces away — and still has zero
`transp`/`hcomp`. `SemiSimplicial4`'s normal form is the one
observable change: each stored filler type now carries its fuel
quantifier, `(m : ℕ) .(f : EqN m <n>) → Dom (frame m <n> 0 f D) →
HSet₀`, with the frame under it stuck at the variable fuel until a
point is eaten.

### 5. Trust posture

- **The REWRITE confluence hand-check** (`Bonak/NatRew.agda`):
  unchanged, and still the file's only extension of definitional
  equality.
- **The termination pragma: gone.** The recursion of the fillers-only
  tower is now checked, with the prefix length as an explicit
  structural column. The residue is `--termination-depth=3` and the
  two fuel arguments in every member's signature.

`νSetF.agda` sits beside `νSet.agda` rather than replacing it: the
swap costs the filler-facing API change (fuel-polymorphic fillers, a
fuel argument on every member), a 2.4× marginal check, and the same
treatment for anything built on top (the νGpd storey, if ported to
this branch). Whether a checked termination argument is worth that
trade for the canonical file is a judgement call the measurements
above are meant to inform.

### 6. Can the fuel column shrink? (same day, later)

Two candidate simplifications, one refuted long since and one tested
now (probes/V4-P05-fuel-no-proof.agda):

**The fuel `n` itself cannot go.** It is the structural column the
whole result rests on: the fuel-less block is the pragma sections'
subject, rejected at --termination-depth 1..10 alike, and §3 of the
fuel section shows no expressible single measure over the existing
arguments works. Nor can `n` be fused into an existing index: retyping
the prefix as `Pre n` moves the k = 0 coercion from the prefix length
to the frame's p-index (`frame m p 0` against `frame m n 0`), which is
`recover-nat-eq` again. Making `n` implicit was considered and
rejected on the LeProp precedent: `EqN` is a defined function and the
proof is irrelevant, so `n` is only recoverable by unification where a
frame application happens to appear in a visible type.

**The proof `.(e : EqN n (p + k))` is syntactically dead weight — and
kept anyway.** It is never used computationally: it closes the three
impossible-fuel clauses and guards `Fil`'s quantifier. `V4-P05` is the
full tower with the proof deleted, the absurd clauses turned into junk
clauses (`layer zero … = hunit`, whence `restr-layer zero … = tt` and
`coh-layer zero … = refl` by η-⊤), and `Fil p k D = (m : ℕ) →
Dom (frame m p k D) → HSet₀`. Everything goes through: no pragma, the
same depth threshold 3 (the junk clauses make no calls, so the call
graph is unchanged), `frame4`'s normal form byte-identical, and the
proof's price measured at 3–7 % (tower + gate: 0.80 s / 3,271 compare
equal / 371 compare irrelevant with the proof, 0.77 s / 3,051 / 142
without).

The reason to keep the proof is what it does to the WRONG-fuel sector
of `Fil`. Without the guard, `frame m p k D` at a wrong fuel reduces
to an inhabited ⊤-tower (the junk layers are `hunit`), so a filler
genuinely carries one HSet-family per wrong fuel and two ν-sets can
differ there: the proof-free `Fil` is strictly bigger than νSet's.
With the guard, the wrong-fuel fibers are functions out of an
irrelevant ⊥ — any two are identified pointwise by an absurd
irrelevant match, under funExt — so the fueled filler type is
equivalent to the unfueled one and the fuel column is structure-free.
(A mathematical remark about the intended νSet ⟷ νSetF comparison,
not a mechanized one.) Since the proof's syntactic cost is one
threaded argument at 3–7 % of the check, νSetF keeps it.

### 7. Why (n, p, k) is the floor

With n ~ p + k the index triple is redundant as information, but not
as patterns: the block is three interlocking recursions, and each
index is the matchable driver of exactly one of them. The
frame-family (frame, restr-frame, coh-frame) matches p — induction on
the layers already assembled, base `p = 0 ↦ hunit`. The
painting-family (painting, restr-painting, coh-painting) matches k —
induction on the levels remaining, base `k = 0` where the stored
filler applies. The layer-family (layer, restr-layer, coh-layer)
matches n — the peel of the prefix, which was always the third
recursion (driven by matching `(D ∷ E)` before the fuel port); n is
that recursion's ℕ-shadow, present because the checker cannot read
the prefix's length under a recursively defined `Pre`.

Dropping k turns painting's base case into `n = p`, and two variables
being equal is not a pattern: the painting-family's base/step
distinction has no clause left to hang on. Dropping p does the same
to frame's base (`n = k`). A relevant "remaining budget" witness that
painting could match instead is an inductive family with done/step
structure — k plus its EqN tie, in disguise — and the LeProp-style ≤
cannot substitute, being ⊤/⊥-valued and therefore structureless by
design. Retyping prefixes as `Pre n` to expel k from the types is §6's
refuted variant (the k = 0 coercion moves to the p-index). So the
signature overhead is exactly: one matchable index per recursive
family, plus the irrelevant witness of §6.

### 8. Backport to Rocq? (same day, later)

No — and the reason is a finding in its own right. Tested on the
bonak-patched-rocq switch (Rocq 9.4+alpha, the patched-CI toolchain);
receipts in probes/V4_P06_rocq_backport.v, a Rocq file among the Agda
probes.

**The guard is the fatal blocker.** νSetF's termination is a
size-change argument — three families descending on three different
columns, sibling edges mostly level, strictness only around composed
cycles, bounded increases at depth 3. Rocq's guard requires every
sibling call to descend strictly on the CALLER's single {struct}
argument, and rejects the block's call skeleton on its first edge:

    Recursive call to layer has principal argument equal to
    "n" instead of "p'".

No struct assignment fares better (frame → layer and painting →
layer pass an equal fuel), and Rocq has no pragma escape. The
workarounds forfeit the design: well-founded recursion (Equations /
Program) unfolds only on closed accessibility witnesses, killing the
variable-index reductions the conversion story needs (the r = 0
restriction, the coercion-free painting base); and restaging on the
fuel is blocked by the suc-written UP-references in the coherence
statements — a coherence at fuel m mentions restrictions at suc m and
suc² m, so staging demands re-indexing every statement downward over
stored per-stratum data, which re-derives the existing Rocq
architecture, Deps records and all. **The stored-strata Rocq original
is the guard-imposed normal form of this construction; the
fillers-only block is the shape only a size-change checker accepts.**
That also locates the discovery: it could only have been made on the
Agda side.

**The other two ingredients port.** NatRew transfers via rewrite
rules on a fresh `Symbol` (Rocq rules cannot attach to `Nat.add`):
addition as a Symbol with its two computation clauses plus the two
extra rules gives all three prefix-former equations of §1 by
`eq_refl` at variable p and k, under `-allow-rewrite-rules` — same
hand-checked-confluence posture as Agda, plus an experimental flag
and the loss of stdlib computation on the symbol. And `EqN` would be
an SProp-valued recursive equality, i.e. the mainline's own LeSProp.v
pattern mirrored back.

There is also nothing to win: the Rocq mainline never paid the
V1-mirror overhead that fillers-only's 8× saving is measured against,
so the perf claim has no direct Rocq analogue.
