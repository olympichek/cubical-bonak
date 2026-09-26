------------------------------------------------------------------------
-- Bonak.νSet — the νSet tower, fillers-only storage with (p , k)
-- indexing and a checked termination argument: the dimension column.
--
-- Storage discipline: only the fillers are stored. `Pre n` is the list
-- of the n fillers below the current level and every other notion —
-- frame, layer, painting, the three restrictions, the three coherences —
-- is a function of the indices and of that list, all in one mutual block.
--
-- Index discipline: relative, (p , k). The dimension n = p + k appears
-- only as the length of the prefix, never as an index of the tower's
-- notions, and every bound is 2-place and relative (q ≤ k, r ≤ q) with
-- dot-irrelevant proofs (Bonak.LeProp). Because `suc q ≤ suc k` reduces
-- to `q ≤ k`, a bound is passed to the next level verbatim: there are no
-- raise/lower lemmas, no stored differences, and no `recover-nat-eq`.
--
-- The prefix's length is where the two disciplines meet: `frame p k`
-- needs p + k fillers, and both indices move. See Bonak.NatRew for the
-- resulting obstruction and the two rewrite rules that remove it.
--
-- The prefix is the only record the construction has, and it is
-- declared without eta so record comparisons do not eta-expand into
-- fieldwise comparisons. Repeated fieldwise comparison multiplies the
-- conversion work down the prefix, so this is a performance constraint,
-- not a typing requirement. Agda's Σ eta cannot be disabled.
-- Without eta a clause only fires on constructor form, so consumers
-- must match the prefix as `(D ∷ E)` even where the proof does not use
-- it (the r = 0 coherence cases).
--
-- Layers are functions `(ε : arity) → B ε`, so component selection is
-- application and the r = 0 restriction case is `l ε` — a
-- definitional fact the construction leans on: it reduces at variable
-- p, k and a variable prefix.
--
-- Equality discipline: PathP-shaped.
-- The layer and painting coherences are dependent paths over the frame
-- coherence, so no statement contains a subst. The Σ-assemblies
-- (coh-frame, coh-painting) are definitional pairing of component
-- paths, the Π-layer step is definitional (a PathP of functions is a
-- function into PathPs), the r = 0 painting coherence is the filler of
-- restr-layer's transport, and the layer coherence is closed by one
-- square filling in the HSet of frames (Bonak.RewLemmas'
-- cohLayer-squareP). restr-layer still transports values along the
-- r = 0 frame coherence — the transport moves to the term level, where
-- fillers connect it to the untransported side.
--
-- Termination is checked through one extra argument per member: the
-- base dimension `n`, a ℕ tied to the member's indices by an irrelevant
-- proof of the recursive equality `EqN n (p + k)` (Bonak.LeProp), so
-- that the prefix's length — the well-founded measure the termination
-- checker cannot read off a recursively defined `Pre` — becomes a
-- plain structural argument. No `{-# TERMINATING #-}`.
--
-- The dimension discipline is forced by definitional equality: each
-- member carries one dimension variable, that of its lowest-dimensional
-- occurrence, and every higher-dimensional frame, layer, painting, or
-- restriction occurrence in its statement is written `suc^j` of it. A free
-- ("output") dimension variable is unusable: a layer's components only
-- reduce at a constructor-form dimension, which pins everything a
-- body builds to the pattern dimension, and a free dimension is not
-- convertible with it. Fillers are the one dimension-polymorphic
-- spot (`Fil` quantifies over the dimension of the point it eats): at
-- k = 0 the point arrives at a variable dimension, and this is what
-- lets `painting`'s base case apply a stored filler with no coercion.
--
-- The EqN proof is computationally inert: it closes three
-- impossible-dimension clauses and guards `Fil`'s quantifier, and the
-- tower typechecks with junk clauses in its place. It is kept because
-- the guard makes the wrong-dimension sector of `Fil` contractible
-- (functions out of an irrelevant ⊥); with junk clauses instead,
-- wrong-dimension frames are inhabited ⊤-towers and fillers carry
-- genuine extra data there.
--
-- The suc-written occurrences make some calls carry dimensions above the
-- caller's own — by up to three constructors, in the coherences'
-- statements — so the call matrices contain bounded increases. The
-- block checks at termination depth 2 (and is rejected at 1).
-- Proof obligations never grow: `EqN`
-- proofs are irrelevant and `EqN (suc n) (suc m)` reduces to
-- `EqN n m`, so the single proof each member holds is passed to every
-- occurrence verbatim.
--
-- The dimension is matched in exactly three places — `layer`,
-- `restr-layer` and `coh-layer` peel one `suc` so their bodies can
-- name the dimension below — and each match adds one absurd clause
-- (`EqN zero (suc _)` is ⊥). Everything else receives its dimension
-- as a determined term, so at closed dimensions every dimension
-- argument reduces away and the compute gate's normal forms carry none
-- of them.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=2 #-}

module Bonak.νSet (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas
open import Bonak.NatRew

HSet₀ : Set₁
HSet₀ = HSet lzero

-- The prefix's cons cell. Parameterized rather than recursive, so it
-- needs no place in the mutual block below.
record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
  no-eta-equality; pattern
  constructor _∷_
  field
    pre : A
    fil : B pre
open Snoc public

------------------------------------------------------------------------
-- The block: signatures
--
-- Argument layout. The dimension is the first argument of every member, so
-- it occupies the same column throughout and the checker reads the
-- descents positionally; then p, k, the irrelevant EqN proof, the
-- prefix, and the member's own arguments.
--
-- The index triple (n, p, k) is redundant as information (n ~ p + k)
-- but minimal as patterns: each index drives one of the block's three
-- recursions — p is matched by the frame-family, k by the
-- painting-family, n by the layer-family (the prefix peel, made
-- structural). A member cannot match a derived index ("n = p" is not
-- a pattern), so all three indices are needed.
------------------------------------------------------------------------

-- The prefix of fillers, and the filler over one.
Pre : ℕ → Set₁
Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

Pre zero    = Unit*
Pre (n +1) = Snoc (Pre n) (Fil n 0)

-- frame(p) at dimension p + k, carried as the argument n ~ p + k.
frame : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k)) → HSet₀

-- A filler eats a point of the full frame at any dimension.
Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → Dom (frame m p k f D) → HSet₀

-- layer(p) at dimension p + k + 1; its dimension argument is its point's.
layer : (n p k : ℕ) .(e : EqN n (p + k +1)) (D : Pre (p + k +1))
        (d : Dom (frame n p (k +1) e D)) → HSet₀

-- painting(p) at dimension p + k, over the filler E.
painting : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k))
           (E : Fil (p + k) 0 D)
           (d : Dom (frame n p k e D)) → HSet₀

-- The three restrictions: dimension p + k + 1 ↦ dimension p + k along
-- the q-th face (q ≤ k); the dimension argument is the output's,
-- the input's is suc of it.
restr-frame : (n p k : ℕ) .(e : EqN n (p + k))
              (D : Pre (p + k +1))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : Dom (frame (n +1) p (k +1) e D))
              → Dom (frame n p k e (pre D))

restr-layer : (n p k : ℕ) .(e : EqN n (p + k +1))
              (D : Pre (p + k +2))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : Dom (frame (n +1) p (k +2) e D))
              (l : Dom (layer (n +1) p (k +1) e D d))
              → Dom (layer n p k e (pre D)
                       (restr-frame n p (k +1) e D (q +1) Hq ε d))

restr-painting : (n p k : ℕ) .(e : EqN n (p + k))
                 (D : Pre (p + k +1)) (E : Fil (p + k +1) 0 D)
                 (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 (d : Dom (frame (n +1) p (k +1) e D))
                 (c : Dom (painting (n +1) p (k +1) e D E d))
                 → Dom (painting n p k e (pre D) (fil D)
                          (restr-frame n p k e D q Hq ε d))

-- The three coherences: the faces q and r commute (r ≤ q ≤ k); the
-- dimension argument is the final output's, two below the point's.
coh-frame : (n p k : ℕ) .(e : EqN n (p + k))
            (D : Pre (p + k +2))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : Dom (frame (n +2) p (k +2) e D))
            → restr-frame n p k e (pre D) q Hq ε
                (restr-frame (n +1) p (k +1) e D r
                   (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
              ≡ restr-frame n p k e (pre D) r (le-trans r q k Hr Hq) ω
                  (restr-frame (n +1) p (k +1) e D (q +1) Hq ε d)

coh-layer : (n p k : ℕ) .(e : EqN n (p + k +1))
            (D : Pre (p + k +3))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : Dom (frame (n +2) p (k +3) e D))
            (l : Dom (layer (n +2) p (k +2) e D d))
            → PathP (λ i → Dom (layer n p k e (pre (pre D))
                       (coh-frame n p (k +1) e D (q +1) Hq (r +1) Hr ε ω d i)))
                (restr-layer n p k e (pre D) q Hq ε
                   (restr-frame (n +1) p (k +2) e D (r +1)
                      (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
                   (restr-layer (n +1) p (k +1) e D r
                      (le-trans r q (k +1) Hr (le-up q k Hq)) ω d l))
                (restr-layer n p k e (pre D) r (le-trans r q k Hr Hq) ω
                   (restr-frame (n +1) p (k +2) e D (q +2) Hq ε d)
                   (restr-layer (n +1) p (k +1) e D (q +1) Hq ε d l))

coh-painting : (n p k : ℕ) .(e : EqN n (p + k))
               (D : Pre (p + k +2))
               (E : Fil (p + k +2) 0 D)
               (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
               (d : Dom (frame (n +2) p (k +2) e D))
               (c : Dom (painting (n +2) p (k +2) e D E d))
               → PathP (λ i → Dom (painting n p k e (pre (pre D)) (fil (pre D))
                          (coh-frame n p k e D q Hq r Hr ε ω d i)))
                   (restr-painting n p k e (pre D) (fil D) q Hq ε
                      (restr-frame (n +1) p (k +1) e D r
                         (le-trans r q (k +1) Hr (le-up q k Hq)) ω d)
                      (restr-painting (n +1) p (k +1) e D E r
                         (le-trans r q (k +1) Hr (le-up q k Hq)) ω d c))
                   (restr-painting n p k e (pre D) (fil D) r
                      (le-trans r q k Hr Hq) ω
                      (restr-frame (n +1) p (k +1) e D (q +1) Hq ε d)
                      (restr-painting (n +1) p (k +1) e D E (q +1) Hq ε d c))

------------------------------------------------------------------------
-- The block: definitions
------------------------------------------------------------------------

frame n zero    k e D = hunit
frame n (p +1) k e D =
  hΣ (frame n p (k +1) e D) (λ d → layer n p k e D d)

-- The prefix is matched, not projected, and the dimension is peeled in step
-- with it: the components live one dimension — one suc — below.
layer zero    p k ()
layer (n +1) p k e (D ∷ E) d =
  hΠ arity (λ ε → painting n p k e D E
                    (restr-frame n p k e (D ∷ E) 0 tt ε d))

painting n p zero    e D E d = E n e d
painting n p (k +1) e D E d =
  hΣ (layer n p k e D d) (λ l → painting n (p +1) k e D E (d , l))

restr-frame n zero    k e D q Hq ε d       = tt
restr-frame n (p +1) k e D q Hq ε (d , l) =
  restr-frame n p (k +1) e D (q +1) Hq ε d ,
  restr-layer n p k e D q Hq ε d l

restr-layer zero    p k ()
restr-layer (n +1) p k e ((D ∷ E₁) ∷ E₂) q Hq ε d l ω =
  subst (λ x → Dom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (n +1) p (k +1) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))

restr-painting n p k       e (D ∷ E₁) E zero    Hq ε d (l , c) = l ε
restr-painting n p zero    e D        E (q +1) ()
restr-painting n p (k +1) e (D ∷ E₁) E (q +1) Hq ε d (l , c) =
  restr-layer n p k e (D ∷ E₁) q Hq ε d l ,
  restr-painting n (p +1) k e (D ∷ E₁) E q Hq ε (d , l) c

coh-frame n zero    k e D q Hq r Hr ε ω d         = refl
coh-frame n (p +1) k e D q Hq r Hr ε ω (d , l) = λ i →
  coh-frame n p (k +1) e D (q +1) Hq (r +1) Hr ε ω d i ,
  coh-layer n p k e D q Hq r Hr ε ω d l i

-- The layer coherence. Layers are Π and a PathP of functions is a
-- function into PathPs, so the θ-component is taken definitionally;
-- each component is one cohLayer-squareP: the two restr-layer
-- transport chains connected along the frame coherence, with the
-- painting coherence as the connecting PathP and the 2-dimensional
-- frame coherence a free Square (frames are HSets).
coh-layer zero    p k ()
coh-layer (n +1) p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω d l = λ i θ →
  let
    P₁ = (D ∷ E₁)
    P₂ = ((D ∷ E₁) ∷ E₂)
    P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
    H₁ = le-trans r q (k +1) Hr (le-up q k Hq)
    H₂ = le-trans r q k Hr Hq
    b = restr-frame (n +2) p (k +2) e P₃ 0 tt θ d
  in
  cohLayer-squareP
    {P = λ x → Dom (painting n p k e D E₁ x)}
    {rf0 = restr-frame n p k e P₁ 0 tt θ}
    {F = restr-painting n p k e P₁ E₂ q Hq ε}
    {G = restr-painting n p k e P₁ E₂ r H₂ ω}
    {E1 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq (r +1) Hr ε ω d}
    {C2 = coh-frame (n +1) p (k +1) e P₃ r H₁ 0 tt ω θ d}
    {D2 = coh-frame (n +1) p (k +1) e P₃ (q +1) Hq 0 tt ε θ d}
    {C1 = coh-frame n p k e P₂ q Hq 0 tt ε θ
            (restr-frame (n +2) p (k +2) e P₃ (r +1) H₁ ω d)}
    {D1 = coh-frame n p k e P₂ r H₂ 0 tt ω θ
            (restr-frame (n +2) p (k +2) e P₃ (q +2) Hq ε d)}
    (coh-painting n p k e P₂ E₃ q Hq r Hr ε ω b (l θ))
    (isSet→Square (isSetDom (frame n p k e D)) _ _ _ _) i

-- The painting coherence. With Π-layers the r = 0 case is the filler
-- of restr-layer's transport (both endpoints reduce to the same
-- restr-painting composite, one transported); the r , q ≥ 1 case pairs
-- the layer coherence with the recursive painting coherence — the pair
-- path is the clause coh-frame unfolds to, so the alignment holds by
-- clause unfolding rather than by a stored-term discipline.
-- Without eta on the prefix the r = 0 reduction (`restr-painting … 0`
-- ↦ `l ω`) fires only when the prefix is a constructor, so this
-- clause has to match it even though the proof does not use it.
coh-painting n p k e ((D ∷ E₁) ∷ E₂) E q Hq zero Hr ε ω d (l , c) =
  subst-filler (λ x → Dom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (n +1) p (k +1) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))
coh-painting n p k e       D          E zero    Hq (r +1) ()
coh-painting n p zero    e D        E (q +1) ()
coh-painting n p (k +1) e ((D ∷ E₁) ∷ E₂) E (q +1) Hq (r +1) Hr
             ε ω d (l , c) = λ i →
  coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω d l i ,
  coh-painting n (p +1) k e ((D ∷ E₁) ∷ E₂) E q Hq r Hr ε ω (d , l) c i

------------------------------------------------------------------------
-- The tower
------------------------------------------------------------------------

-- The full frame at dimension n: the one whose index is the length,
-- at the dimension that IS the length.
fullframe : {n : ℕ} (D : Pre n) → HSet₀
fullframe {n} D = frame n n 0 (eqN-refl n) D

record νSet→ (n : ℕ) (D : Pre n) : Set₁ where
  coinductive
  constructor _∷ν_
  field
    this : Fil n 0 D
    next : νSet→ (n +1) (D ∷ this)
open νSet→ public

νSets : Set₁
νSets = νSet→ 0 tt*
