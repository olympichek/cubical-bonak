# V3 — groupoid-rew νSet/νGpd (branch `rew`)

The validated RewTrick discipline (~/bonak/cubical-probes/RewTrick.agda,
gates G1–G7; notes/PathP-self-similarity.md §5b): coherences stated
POINTWISE ON TRANSPORTED INHABITANTS — nested subst chains, never
∙-composites — so reassociation never arises. Diverges from V1 (`main`)
as follows.

## Discipline

- A level-2 coherence is
  `subst P r₃ (subst P r₂ (subst P r₁ c)) ≡ subst P s₂ (subst P s₁ c)`
  — bracket-free (nested application is strictly associative).
- funExt round-trips are definitional (G4), so with Π-layers the
  layer level IS the pointwise level: zero bridges.
- Level shift (G6): keep each level-2 coherence as a transport in the
  path family `λ u → F c ≡ u`, chain by nesting; pay ONE interface
  lemma per level, only at boundaries where a ∙-composite is
  genuinely demanded (the Σ≡ assembly in mkCohFrames is the main one).
- `mkCoh2FrameType` (νGpd): stated as ∀-pointwise transport-chain
  equations on frame points — replaces V1's hexagon of ∙-composites
  entirely; `rew-cohLayer33`'s Hpath premise becomes a chain equation
  consumed by cong-of-subst, no ∙-assoc.

## Warts to watch (G3)

- transp-refl is identity on neutrals only for parameterless
  inductives and Π over them; Σ-NEUTRALS STICK. Keep families
  concrete and inputs constructor-headed at the computation gates.
- Expected win at the SemiSimplicial4 gate: the V1 normal form's
  transp/hcomp residue should shrink (fewer ∙, fewer hcomp trees).

## Gates

1. νSet tower typechecks; count aux lemmas vs V1 (RewTrick measured
   0 vs 6 at level 2 on the toy; measure the real tower).
2. SemiSimplicial4 normal-form size + residue census vs V1/V2.
3. Timing vs V1/V2.
