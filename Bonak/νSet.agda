------------------------------------------------------------------------
-- Bonak.νSet — the νSet tower, fillers-only storage with (p , k)
-- indexing and a CHECKED termination argument: the fuel column.
--
-- Storage discipline: only the fillers are stored.  `Pre n` is the list
-- of the n fillers below the current level and every other notion —
-- frame, layer, painting, the three restrictions, the three coherences —
-- is a FUNCTION of the indices and of that list, all in one mutual
-- block.  No Deps records, no Extension inductives, no stored strata.
--
-- Index discipline: relative, (p , k).  The dimension n = p + k appears
-- only as the LENGTH of the prefix, never as an index of the tower's
-- notions, and every bound is 2-place and relative (q ≤ k, r ≤ q) with
-- dot-irrelevant proofs (Bonak.LeProp).  Because `suc q ≤ suc k` reduces
-- to `q ≤ k`, a bound is passed to the next level verbatim: there are no
-- raise/lower lemmas, no stored differences, and no `recover-nat-eq`.
--
-- The prefix's length is where the two disciplines meet: `frame p k`
-- needs p + k fillers, and both indices move.  See Bonak.NatRew for the
-- resulting obstruction and the two rewrite rules that remove it.
--
-- The prefix is the only record the construction has, and it is
-- declared without eta: eta-expansion of record comparisons is the
-- known conversion hazard of this development (THE ETA FIX, see
-- PORTING-NOTES), and a no-eta prefix measures ~1.8× cheaper than the
-- same construction over Agda's Σ, whose eta has no off switch.
-- Without eta a clause only fires on constructor form, so consumers
-- must match the prefix as `(D ∷ E)` even where the proof does not use
-- it (the r = 0 coherence cases).
--
-- Layers are functions `(ε : arity) → B ε` (V1 decision 1), so `nth` is
-- application and the r = 0 restriction case is `l ε` — it reduces at a
-- variable prefix, which is what the bottom-index hazard demands.
--
-- Equality discipline: PathP-shaped (DESIGN-V2 in the pathp worktree).
-- The layer and painting coherences are dependent paths over the frame
-- coherence, so no statement contains a subst.  The Σ-assemblies
-- (coh-frame, coh-painting) are definitional pairing of component
-- paths, the Π-layer step is definitional (a PathP of functions is a
-- function into PathPs), the r = 0 painting coherence is the filler of
-- restr-layer's transport, and the layer coherence is closed by one
-- square filling in the HSet of frames (Bonak.RewLemmas'
-- cohLayer-squareP).  restr-layer still transports values along the
-- r = 0 frame coherence — the transport moves to the term level, where
-- fillers connect it to the untransported side.
--
-- Termination is checked through one extra argument per member: the
-- fuel `n`, a ℕ tied to the member's base dimension by an irrelevant
-- proof of the recursive equality `EqN n (p + k)` (Bonak.EqProp), so
-- that the prefix's length — the well-founded measure the termination
-- checker cannot read off a recursively defined `Pre` — becomes a
-- plain structural argument.  No `{-# TERMINATING #-}`.
--
-- The fuel discipline is forced by definitional equality
-- (probes/V4-P03-output-fuel.agda): each member carries exactly ONE
-- fuel variable, the fuel of its LOWEST-dimensional occurrence, and
-- every higher-dimensional frame / layer / painting / restriction
-- occurrence in its statement is written `suc^j` of it.  A free
-- ("output") fuel variable is unusable: a layer's components only
-- reduce at a constructor-form fuel, which pins everything a body
-- builds to the pattern fuel, and a free fuel is not convertible with
-- it.  Fillers are the one fuel-polymorphic spot (`Fil` quantifies
-- over the fuel of the point it eats): at k = 0 the point arrives at a
-- variable fuel, and this is what lets `painting`'s base case apply a
-- stored filler with no coercion.
--
-- The EqN proof is computationally inert — it closes three
-- impossible-fuel clauses and guards `Fil`'s quantifier — and the
-- tower typechecks without it, with junk clauses instead
-- (probes/V4-P05-fuel-no-proof.agda).  It is kept because it is what
-- makes the wrong-fuel sector of `Fil` contractible (functions out of
-- an irrelevant ⊥): without it, wrong-fuel frames are inhabited
-- ⊤-towers and fillers carry genuine extra data there.
--
-- The suc-written occurrences make some calls carry fuels ABOVE the
-- caller's own — by up to three constructors, in the coherences'
-- statements — so the call matrices contain bounded increases, and the
-- checker needs --termination-depth ≥ 3 to compose them (this file is
-- rejected at 2; probes/V4-P04-depth.agda shows the mechanism on a
-- model of exactly these calls).  Proof obligations never grow: `EqN`
-- proofs are irrelevant and `EqN (suc n) (suc m)` reduces to
-- `EqN n m`, so the single proof each member holds is passed to every
-- occurrence verbatim.
--
-- Fuel is matched in exactly three places — `layer`, `restr-layer` and
-- `coh-layer` peel one `suc` so their bodies can name the dimension
-- below — and each match adds one absurd clause (`EqN zero (suc _)` is
-- ⊥).  Everything else receives its fuel as a determined term, so at
-- closed dimensions every fuel reduces away and the compute gate's
-- normal forms are fuel-free.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=3 #-}

module Bonak.νSet (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.EqProp
open import Bonak.RewLemmas
open import Bonak.NatRew

HSet₀ : Set₁
HSet₀ = HSet lzero

-- The prefix's cons cell.  Parameterized rather than recursive, so it
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
-- ARGUMENT LAYOUT.  The fuel is the FIRST argument of every member, so
-- it occupies the same column throughout and the checker reads the
-- descents positionally; then p, k, the irrelevant EqN proof, the
-- prefix, and the member's own arguments.
--
-- The index triple (n, p, k) is redundant as information (n ~ p + k)
-- but minimal as patterns: each index drives one of the block's three
-- recursions — p is matched by the frame-family, k by the
-- painting-family, n by the layer-family (the prefix peel, made
-- structural).  A member cannot match a derived index ("n = p" is not
-- a pattern), so none of the three can be dropped; see V4-REPORT.md.
------------------------------------------------------------------------

-- The prefix of fillers, and the filler over one.
Pre : ℕ → Set₁
Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

Pre zero    = Unit*
Pre (suc n) = Snoc (Pre n) (Fil n 0)

-- frame(p) at dimension p + k, at fuel n ~ p + k.
frame : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k)) → HSet₀

-- A filler eats a point of the full frame AT ANY FUEL.
Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → Dom (frame m p k f D) → HSet₀

-- layer(p) at dimension p + k + 1; its fuel is its point's.
layer : (n p k : ℕ) .(e : EqN n (suc (p + k))) (D : Pre (suc (p + k)))
        (d : Dom (frame n p (suc k) e D)) → HSet₀

-- painting(p) at dimension p + k, over the filler E.
painting : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k))
           (E : Fil (p + k) 0 D)
           (d : Dom (frame n p k e D)) → HSet₀

-- The three restrictions: dimension p + k + 1 ↦ dimension p + k along
-- the q-th face (q ≤ k); the fuel is the OUTPUT's, the input's is
-- suc of it.
restr-frame : (n p k : ℕ) .(e : EqN n (p + k))
              (D : Pre (suc (p + k)))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : Dom (frame (suc n) p (suc k) e D))
              → Dom (frame n p k e (pre D))

restr-layer : (n p k : ℕ) .(e : EqN n (suc (p + k)))
              (D : Pre (suc (suc (p + k))))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : Dom (frame (suc n) p (suc (suc k)) e D))
              (l : Dom (layer (suc n) p (suc k) e D d))
              → Dom (layer n p k e (pre D)
                       (restr-frame n p (suc k) e D (suc q) Hq ε d))

restr-painting : (n p k : ℕ) .(e : EqN n (p + k))
                 (D : Pre (suc (p + k))) (E : Fil (suc (p + k)) 0 D)
                 (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 (d : Dom (frame (suc n) p (suc k) e D))
                 (c : Dom (painting (suc n) p (suc k) e D E d))
                 → Dom (painting n p k e (pre D) (fil D)
                          (restr-frame n p k e D q Hq ε d))

-- The three coherences: the faces q and r commute (r ≤ q ≤ k); the
-- fuel is the final output's, two below the point's.
coh-frame : (n p k : ℕ) .(e : EqN n (p + k))
            (D : Pre (suc (suc (p + k))))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : Dom (frame (suc (suc n)) p (suc (suc k)) e D))
            → restr-frame n p k e (pre D) q Hq ε
                (restr-frame (suc n) p (suc k) e D r
                   (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
              ≡ restr-frame n p k e (pre D) r (le-trans r q k Hr Hq) ω
                  (restr-frame (suc n) p (suc k) e D (suc q) Hq ε d)

coh-layer : (n p k : ℕ) .(e : EqN n (suc (p + k)))
            (D : Pre (suc (suc (suc (p + k)))))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : Dom (frame (suc (suc n)) p (suc (suc (suc k))) e D))
            (l : Dom (layer (suc (suc n)) p (suc (suc k)) e D d))
            → PathP (λ i → Dom (layer n p k e (pre (pre D))
                       (coh-frame n p (suc k) e D (suc q) Hq (suc r) Hr
                          ε ω d i)))
                (restr-layer n p k e (pre D) q Hq ε
                   (restr-frame (suc n) p (suc (suc k)) e D (suc r)
                      (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                   (restr-layer (suc n) p (suc k) e D r
                      (le-trans r q (suc k) Hr (le-up q k Hq)) ω d l))
                (restr-layer n p k e (pre D) r (le-trans r q k Hr Hq) ω
                   (restr-frame (suc n) p (suc (suc k)) e D (suc (suc q))
                      Hq ε d)
                   (restr-layer (suc n) p (suc k) e D (suc q) Hq ε d l))

coh-painting : (n p k : ℕ) .(e : EqN n (p + k))
               (D : Pre (suc (suc (p + k))))
               (E : Fil (suc (suc (p + k))) 0 D)
               (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
               (d : Dom (frame (suc (suc n)) p (suc (suc k)) e D))
               (c : Dom (painting (suc (suc n)) p (suc (suc k)) e D E d))
               → PathP (λ i → Dom (painting n p k e (pre (pre D))
                          (fil (pre D))
                          (coh-frame n p k e D q Hq r Hr ε ω d i)))
                   (restr-painting n p k e (pre D) (fil D) q Hq ε
                      (restr-frame (suc n) p (suc k) e D r
                         (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                      (restr-painting (suc n) p (suc k) e D E r
                         (le-trans r q (suc k) Hr (le-up q k Hq)) ω d c))
                   (restr-painting n p k e (pre D) (fil D) r
                      (le-trans r q k Hr Hq) ω
                      (restr-frame (suc n) p (suc k) e D (suc q) Hq ε d)
                      (restr-painting (suc n) p (suc k) e D E (suc q)
                         Hq ε d c))

------------------------------------------------------------------------
-- The block: definitions
------------------------------------------------------------------------

frame n zero    k e D = hunit
frame n (suc p) k e D =
  hΣ (frame n p (suc k) e D) (λ d → layer n p k e D d)

-- The prefix is matched, not projected, and the fuel is peeled in step
-- with it: the components live one dimension — one suc — below.
layer zero    p k ()
layer (suc n) p k e (D ∷ E) d =
  hΠ arity (λ ε → painting n p k e D E
                    (restr-frame n p k e (D ∷ E) 0 tt ε d))

painting n p zero    e D E d = E n e d
painting n p (suc k) e D E d =
  hΣ (layer n p k e D d) (λ l → painting n (suc p) k e D E (d , l))

restr-frame n zero    k e D q Hq ε d       = tt
restr-frame n (suc p) k e D q Hq ε (d , l) =
  restr-frame n p (suc k) e D (suc q) Hq ε d ,
  restr-layer n p k e D q Hq ε d l

restr-layer zero    p k ()
restr-layer (suc n) p k e ((D ∷ E₁) ∷ E₂) q Hq ε d l ω =
  subst (λ x → Dom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (suc n) p (suc k) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))

restr-painting n p k       e (D ∷ E₁) E zero    Hq ε d (l , c) = l ε
restr-painting n p zero    e D        E (suc q) ()
restr-painting n p (suc k) e (D ∷ E₁) E (suc q) Hq ε d (l , c) =
  restr-layer n p k e (D ∷ E₁) q Hq ε d l ,
  restr-painting n (suc p) k e (D ∷ E₁) E q Hq ε (d , l) c

coh-frame n zero    k e D q Hq r Hr ε ω d         = refl
coh-frame n (suc p) k e D q Hq r Hr ε ω (d , l) i =
  coh-frame n p (suc k) e D (suc q) Hq (suc r) Hr ε ω d i ,
  coh-layer n p k e D q Hq r Hr ε ω d l i

-- The layer coherence.  Layers are Π and a PathP of functions is a
-- function into PathPs, so the θ-component is taken definitionally;
-- each component is one cohLayer-squareP: the two restr-layer
-- transport chains connected along the frame coherence, with the
-- painting coherence as the connecting PathP and the 2-dimensional
-- frame coherence a free Square (frames are HSets).  Every path
-- implicit of cohLayer-squareP has to be given: the goal only
-- exposes them after unfolding two nested restr-layer clauses, and
-- Agda's unifier gives up there (the V1 decision-8 spots, at scale).
coh-layer zero    p k ()
coh-layer (suc n) p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω d l i θ =
  cohLayer-squareP
    {P = λ x → Dom (painting n p k e D E₁ x)}
    {S2 = λ m → Dom (painting (suc n) p (suc k) e P₁ E₂ m)}
    {S3 = λ m → Dom (painting (suc n) p (suc k) e P₁ E₂ m)}
    {rf0 = λ x → restr-frame n p k e P₁ 0 tt θ x}
    {rfF = λ m → restr-frame n p k e P₁ q Hq ε m}
    {rfG = λ m → restr-frame n p k e P₁ r H₂ ω m}
    {F = λ m c → restr-painting n p k e P₁ E₂ q Hq ε m c}
    {G = λ m c → restr-painting n p k e P₁ E₂ r H₂ ω m c}
    {E1 = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc r) Hr ε ω d}
    {m1 = restr-frame (suc n) p (suc k) e P₂ r H₁ ω (b θ)}
    {m2 = restr-frame (suc n) p (suc k) e P₂ 0 tt θ dR}
    {C2 = coh-frame (suc n) p (suc k) e P₃ r H₁ 0 tt ω θ d}
    {n1 = restr-frame (suc n) p (suc k) e P₂ (suc q) Hq ε (b θ)}
    {n2 = restr-frame (suc n) p (suc k) e P₂ 0 tt θ dE}
    {D2 = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq 0 tt ε θ d}
    {C1 = coh-frame n p k e P₂ q Hq 0 tt ε θ dR}
    {D1 = coh-frame n p k e P₂ r H₂ 0 tt ω θ dE}
    {K = coh-frame n p k e P₂ q Hq r Hr ε ω (b θ)}
    {aL = restr-painting (suc n) p (suc k) e P₂ E₃ r H₁ ω (b θ) (l θ)}
    {aR = restr-painting (suc n) p (suc k) e P₂ E₃ (suc q) Hq ε
            (b θ) (l θ)}
    (coh-painting n p k e P₂ E₃ q Hq r Hr ε ω (b θ) (l θ))
    (isSet→Square (isSetDom (frame n p k e D)) _ _ _ _)
    i
  where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  -- the ω-restriction of d used by the outer restr-layer on each side,
  dR = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc r) H₁ ω d
  dE = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc (suc q)) Hq ε d
  -- and its θ-restriction, where the painting coherence applies.
  b : (θ : arity) → Dom (frame (suc (suc n)) p (suc (suc k)) e P₂)
  b θ = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ 0 tt θ d

-- The painting coherence.  With Π-layers the r = 0 case is the filler
-- of restr-layer's transport (both endpoints reduce to the same
-- restr-painting composite, one transported); the r , q ≥ 1 case pairs
-- the layer coherence with the recursive painting coherence — the pair
-- path IS the clause coh-frame unfolds to, so the alignment holds by
-- clause unfolding rather than by a stored-term discipline.
-- Without eta on the prefix the r = 0 reduction (`restr-painting … 0`
-- ↦ `l ω`) fires only when the prefix is a constructor, so this
-- clause has to match it even though the proof does not use it.
coh-painting n p k e ((D ∷ E₁) ∷ E₂) E q Hq zero Hr ε ω d (l , c) =
  subst-filler (λ x → Dom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (suc n) p (suc k) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))
coh-painting n p k e       D          E zero    Hq (suc r) ()
coh-painting n p zero    e D        E (suc q) ()
coh-painting n p (suc k) e ((D ∷ E₁) ∷ E₂) E (suc q) Hq (suc r) Hr ε ω
             d (l , c) i =
  coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω d l i ,
  coh-painting n (suc p) k e ((D ∷ E₁) ∷ E₂) E q Hq r Hr ε ω (d , l) c i

------------------------------------------------------------------------
-- The tower
------------------------------------------------------------------------

-- The full frame at dimension n: the one whose index is the length,
-- at the fuel that IS the length.
fullframe : {n : ℕ} (D : Pre n) → HSet₀
fullframe {n} D = frame n n 0 (eqN-refl n) D

record νSet→ (n : ℕ) (D : Pre n) : Set₁ where
  coinductive
  constructor _∷ν_
  field
    this : Fil n 0 D
    next : νSet→ (suc n) (D ∷ this)
open νSet→ public

νSets : Set₁
νSets = νSet→ 0 tt*
