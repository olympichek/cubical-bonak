------------------------------------------------------------------------
-- agents.probes.V4-P03-output-dimension — the "output dimension"
-- route of V4-REPORT.md §"The dimension column" item 4: restrictions
-- and coherences take their result's dimension as a universally
-- quantified argument, so no signature ever writes `predℕ` and the
-- caller instantiates the output dimension with a pattern-derived
-- value.
--
-- This probe tests the route's CONVERSION obligations, on a mini-tower
-- with the real types (HSet frames, Π-layers, dimension-polymorphic
-- fillers) and the real bodies of the structural members; the members
-- whose bodies are irrelevant to the question are closed with a
-- postulated inhabitant, and the block carries a TERMINATING pragma —
-- termination is NOT this probe's question, definitional equality is.
--
-- `Wall` is the route as sketched: every restriction takes its output
-- dimension `m` as a free variable.  Its `restr-painting` q = 0 clause is
-- `l ε` — and `l`'s type only reduces after matching the INPUT dimension as
-- `suc n₀`, which pins the layer's components to the pattern dimension n₀,
-- while the signature promises them at the free dimension m.  n₀ and m are
-- propositionally equal (both are EqN-related to p + k) but not
-- convertible, and no cast between the two is expressible without the
-- recursive coercions the fillers-only design exists to avoid.
--
-- OUTCOME: the two walls force the single suc-written dimension per member
-- (dimension variant (a) of the report), whose statement-borne up-calls the
-- checker composes at --termination-depth ≥ 3 — see
-- agents/probes/V4-P04-depth.agda for the mechanism and Bonak.νSet for the
-- resulting pragma-free tower.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=2 #-}

module agents.probes.V4-P03-output-dimension where

open import Bonak.Prelude
open import Bonak.LeProp using (⊥)
open import Bonak.NatRew

postulate arity : Set

-- Scaffold for bodies whose content is irrelevant to the probe.
postulate ANY : ∀ {ℓ} {A : Set ℓ} → A

-- The recursive equality on ℕ (the dimension attempt's replacement for
-- `injSuc`-peeled paths): `EqN (suc n) (suc m)` REDUCES to `EqN n m`,
-- so a proof is passed down verbatim, and it is used irrelevantly
-- throughout, so no two proofs are ever compared.
EqN : ℕ → ℕ → Set
EqN zero    zero    = ⊤
EqN zero    (suc m) = ⊥
EqN (suc n) zero    = ⊥
EqN (suc n) (suc m) = EqN n m

------------------------------------------------------------------------
-- The route as sketched: free output dimensions.
------------------------------------------------------------------------

module Wall where

  record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
    no-eta-equality; pattern
    constructor _∷_
    field
      pre : A
      fil : B pre
  open Snoc public

  Pre : ℕ → Set₁
  Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

  Pre zero    = Unit*
  Pre (suc n) = Snoc (Pre n) (Fil n 0)

  frame : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k)) → HSet lzero

  -- Dimension-polymorphic filler: a stored filler eats a point at
  -- any dimension.
  Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → Dom (frame m p k f D) → HSet lzero

  layer : (n p k : ℕ) .(e : EqN n (suc (p + k))) (D : Pre (suc (p + k)))
          (d : Dom (frame n p (suc k) e D)) → HSet lzero

  painting : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k))
             (E : Fil (p + k) 0 D)
             (d : Dom (frame n p k e D)) → HSet lzero

  restr-frame : (n m p k : ℕ)
                .(e : EqN n (suc (p + k))) .(em : EqN m (p + k))
                (D : Pre (suc (p + k))) (q : ℕ) (ε : arity)
                (d : Dom (frame n p (suc k) e D))
                → Dom (frame m p k em (pre D))

  restr-layer : (n m p k : ℕ)
                .(e : EqN n (suc (suc (p + k)))) .(em : EqN m (suc (p + k)))
                (D : Pre (suc (suc (p + k)))) (q : ℕ) (ε : arity)
                (d : Dom (frame n p (suc (suc k)) e D))
                (l : Dom (layer n p (suc k) e D d))
                → Dom (layer m p k em (pre D)
                         (restr-frame n m p (suc k) e em D (suc q) ε d))

  restr-painting : (n m p k : ℕ)
                   .(e : EqN n (suc (p + k))) .(em : EqN m (p + k))
                   (D : Pre (suc (p + k))) (E : Fil (suc (p + k)) 0 D)
                   (q : ℕ) (ε : arity)
                   (d : Dom (frame n p (suc k) e D))
                   (c : Dom (painting n p (suc k) e D E d))
                   → Dom (painting m p k em (pre D) (fil D)
                            (restr-frame n m p k e em D q ε d))

  {-# TERMINATING #-}
  frame n zero    k e D = hunit
  frame n (suc p) k e D =
    hΣ (frame n p (suc k) e D) (λ d → layer n p k e D d)

  layer zero    p k ()
  layer (suc n) p k e (D ∷ E) d =
    hΠ arity (λ ε → painting n p k e D E
                      (restr-frame (suc n) n p k e e (D ∷ E) 0 ε d))

  painting n p zero    e D E d = E n e d
  painting n p (suc k) e D E d =
    hΣ (layer n p k e D d) (λ l → painting n (suc p) k e D E (d , l))

  restr-frame n m zero    k e em D q ε d       = tt
  restr-frame n m (suc p) k e em D q ε (d , l) =
    restr-frame n m p (suc k) e em D (suc q) ε d ,
    restr-layer n m p k e em D q ε d l

  restr-layer n m p k e em D q ε d l = ANY

  -- THE TEST.  The q = 0 clause: `l`'s type reduces only after the
  -- input dimension is matched, which produces the layer's
  -- components at the pattern dimension n₀ where the signature
  -- demands the free dimension m.
  -- REJECTED: `n₀ != m of type ℕ` — flip TEST-WALL to reproduce.
  restr-painting zero     m p k ()
  restr-painting (suc n₀) m p k e em (D ∷ E₁) E zero    ε d (l , c) = wall
    where postulate wall : _   -- TEST-WALL: replace by `l ε`
  restr-painting (suc n₀) m p k e em (D ∷ E₁) E (suc q) ε d c = ANY

------------------------------------------------------------------------
-- The repair forced by the wall: `restr-painting`'s single dimension
-- variable is its OUTPUT's, the input is written `suc m`.  Its q = 0
-- clause then typechecks — `layer`'s clause fires at `suc m` and
-- produces components at exactly the promised dimension m.  The question is
-- whether the repair stops there: `restr-layer` still carries a free
-- output dimension here, and its own body meets the same wall.
------------------------------------------------------------------------

module Cascade where

  record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
    no-eta-equality; pattern
    constructor _∷_
    field
      pre : A
      fil : B pre
  open Snoc public

  Pre : ℕ → Set₁
  Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

  Pre zero    = Unit*
  Pre (suc n) = Snoc (Pre n) (Fil n 0)

  frame : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k)) → HSet lzero

  Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → Dom (frame m p k f D) → HSet lzero

  layer : (n p k : ℕ) .(e : EqN n (suc (p + k))) (D : Pre (suc (p + k)))
          (d : Dom (frame n p (suc k) e D)) → HSet lzero

  painting : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k))
             (E : Fil (p + k) 0 D)
             (d : Dom (frame n p k e D)) → HSet lzero

  restr-frame : (n m p k : ℕ)
                .(e : EqN n (suc (p + k))) .(em : EqN m (p + k))
                (D : Pre (suc (p + k))) (q : ℕ) (ε : arity)
                (d : Dom (frame n p (suc k) e D))
                → Dom (frame m p k em (pre D))

  restr-layer : (n m p k : ℕ)
                .(e : EqN n (suc (suc (p + k)))) .(em : EqN m (suc (p + k)))
                (D : Pre (suc (suc (p + k)))) (q : ℕ) (ε : arity)
                (d : Dom (frame n p (suc (suc k)) e D))
                (l : Dom (layer n p (suc k) e D d))
                → Dom (layer m p k em (pre D)
                         (restr-frame n m p (suc k) e em D (suc q) ε d))

  -- Repaired: input dimension written `suc m` from the output's variable.
  restr-painting : (m p k : ℕ) .(em : EqN m (p + k))
                   (D : Pre (suc (p + k))) (E : Fil (suc (p + k)) 0 D)
                   (q : ℕ) (ε : arity)
                   (d : Dom (frame (suc m) p (suc k) em D))
                   (c : Dom (painting (suc m) p (suc k) em D E d))
                   → Dom (painting m p k em (pre D) (fil D)
                            (restr-frame (suc m) m p k em em D q ε d))

  -- The r = 0 frame coherence, as `restr-layer`'s body needs it: with
  -- both restrictions' dimensions free, the two sides restrict through
  -- intermediate objects whose dimensions differ, so the statement carries
  -- one intermediate dimension per side (mL, mR) plus the common final m₂.
  coh-frame : (n mL mR m₂ p k : ℕ)
              .(e : EqN n (suc (suc (p + k))))
              .(eL : EqN mL (suc (p + k))) .(eR : EqN mR (suc (p + k)))
              .(em₂ : EqN m₂ (p + k))
              (D : Pre (suc (suc (p + k)))) (q : ℕ) (ε ω : arity)
              (d : Dom (frame n p (suc (suc k)) e D))
              → restr-frame mL m₂ p k eL em₂ (pre D) q ε
                  (restr-frame n mL p (suc k) e eL D 0 ω d)
                ≡ restr-frame mR m₂ p k eR em₂ (pre D) 0 ω
                    (restr-frame n mR p (suc k) e eR D (suc q) ε d)

  {-# TERMINATING #-}
  frame n zero    k e D = hunit
  frame n (suc p) k e D =
    hΣ (frame n p (suc k) e D) (λ d → layer n p k e D d)

  layer zero    p k ()
  layer (suc n) p k e (D ∷ E) d =
    hΠ arity (λ ε → painting n p k e D E
                      (restr-frame (suc n) n p k e e (D ∷ E) 0 ε d))

  painting n p zero    e D E d = E n e d
  painting n p (suc k) e D E d =
    hΣ (layer n p k e D d) (λ l → painting n (suc p) k e D E (d , l))

  restr-frame n m zero    k e em D q ε d       = tt
  restr-frame n m (suc p) k e em D q ε (d , l) =
    restr-frame n m p (suc k) e em D (suc q) ε d ,
    restr-layer n m p k e em D q ε d l

  -- THE TEST.  The real body of restr-layer is a function of the arity
  -- ω — but its result type `Dom (layer m …)` is STUCK at the free
  -- output dimension m, so the clause cannot even take ω:
  --
  --   Cannot eliminate type Dom (layer m p k _ (D ∷ E₁) …)
  --   with variable pattern ω
  --
  -- (flip TEST-WALL to reproduce).  The body would have to match its
  -- input dimension two deep — `l`'s layer fires at suc (suc n''), pinning
  -- everything it builds to the n''-chain — while the goal lives on
  -- the chain of m; the chains never meet.  So restr-layer must be
  -- suc-written too, and then coh-frame's two intermediate dimensions are
  -- forced equal (the outer restriction's input IS the inner's
  -- output), collapsing the whole discipline into single suc-written
  -- dimensions: variant (a) of the report, already rejected by the
  -- termination checker.
  restr-layer n m p k e em D q ε d l = wall
    where postulate wall : _   -- TEST-WALL: replace by the real body
  {-
  restr-layer (suc (suc n'')) m p k e em ((D ∷ E₁) ∷ E₂) q ε d l ω =
    subst (λ x → Dom (painting n'' p k em D E₁ x))
      (coh-frame (suc (suc n'')) (suc n'') (suc n'') n'' p k e e e em
         ((D ∷ E₁) ∷ E₂) q ε ω d)
      (restr-painting n'' p k em (D ∷ E₁) E₂ q ε
        (restr-frame (suc (suc n'')) (suc n'') p (suc k) e e
           ((D ∷ E₁) ∷ E₂) 0 ω d)
        (l ω))
  restr-layer zero       m p k ()
  restr-layer (suc zero) m p k ()
  -}

  restr-painting m p k em (D ∷ E₁) E zero    ε d (l , c) = l ε
  restr-painting m p k em (D ∷ E₁) E (suc q) ε d c = ANY

  coh-frame n mL mR m₂ p k e eL eR em₂ D q ε ω d = ANY
