------------------------------------------------------------------------
-- Bonak.νSet — the νSet tower, fillers-only storage with (p , k)
-- indexing.  The prefix of fillers is a per-level record WITHOUT eta.
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
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=2 #-}

module Bonak.νSet (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
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
-- One mutual block, in Agda's layout-inferred style.  `Pre` and `Fil`
-- are defined as soon as they are declared: the later signatures project
-- out of a prefix (`pre D`, `fil D`), which needs `Pre` to reduce, and a
-- merely declared function does not reduce.
--
-- ARGUMENT LAYOUT.  Agda's termination checker compares caller and
-- callee arguments BY POSITION, so a descent is seen only where the
-- descending argument occupies the same column on both sides.  This
-- construction's well-founded measure is the prefix shrinking (`fst D`,
-- under layer / restr-layer / coh-layer), so the prefix sits in a fixed
-- column in every member — hence the argument order
--
--     p , k , D , [E] , q , Hq , r , Hr , ε , ω , d , l/c
--
-- with the faces and their bounds AFTER the prefix, rather than the
-- reading order (p k q r … D d) the statements suggest.  Clauses match
-- the prefix (`(D , E)`) instead of projecting it, for the same reason.
--
-- TERMINATION IS NOT ESTABLISHED, and six of the eleven members carry
-- `{-# TERMINATING #-}`.  The recursion is well-founded — every cycle
-- either shrinks the prefix or decreases p or k — but the shrinking one
-- is invisible to a size-change analysis: the level that decreases is
-- the prefix's LENGTH, which under (p,k) indexing is p + k, an
-- expression in the types and not an argument of anything.  Alice's
-- absolutely-indexed block passes precisely because that level is her
-- first argument.  Measured, not guessed: the block is rejected at
-- --termination-depth 2..6; with the prefix column aligned and matched
-- the rejected set shrinks from all of {frame, layer, painting,
-- restr-frame, restr-layer, coh-frame} to six members; removing any
-- single one of restr-layer's four calls makes it pass, which is what
-- fixing one edge (V1 decision 3's abstraction of restr-layer over its
-- r = 0 coherence) does — it moves three more members across but not
-- the rest.  This costs nothing at the measured level: pragma'd
-- definitions still reduce, and the compute gate passes.
------------------------------------------------------------------------

-- The prefix of fillers, and the filler over one.
Pre : ℕ → Set₁
Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

Pre zero    = Unit*
Pre (suc n) = Snoc (Pre n) (Fil n 0)

-- frame(p) at dimension p + k.
frame : (p k : ℕ) (D : Pre (p + k)) → HSet₀

-- A filler at dimension n is a family over the FULL frame at n, i.e.
-- the frame whose index equals the prefix length: (p , k) = (n , 0).
Fil p k D = Dom (frame p k D) → HSet₀

-- layer(p) at dimension p + k + 1 (so it can peel the top filler).
layer : (p k : ℕ) (D : Pre (suc (p + k)))
        (d : Dom (frame p (suc k) D)) → HSet₀

-- painting(p) at dimension p + k, over the filler E.
painting : (p k : ℕ) (D : Pre (p + k)) (E : Fil (p + k) 0 D)
           (d : Dom (frame p k D)) → HSet₀

-- The three restrictions: dimension p + k + 1 ↦ dimension p + k, along
-- the q-th face, q relative to p (q ≤ k).
restr-frame : (p k : ℕ) (D : Pre (suc (p + k)))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : Dom (frame p (suc k) D))
              → Dom (frame p k (pre D))

restr-layer : (p k : ℕ) (D : Pre (suc (suc (p + k))))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : Dom (frame p (suc (suc k)) D))
              (l : Dom (layer p (suc k) D d))
              → Dom (layer p k (pre D)
                       (restr-frame p (suc k) D (suc q) Hq ε d))

restr-painting : (p k : ℕ) (D : Pre (suc (p + k)))
                 (E : Fil (suc (p + k)) 0 D)
                 (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 (d : Dom (frame p (suc k) D))
                 (c : Dom (painting p (suc k) D E d))
                 → Dom (painting p k (pre D) (fil D)
                          (restr-frame p k D q Hq ε d))

-- The three coherences: the faces q and r commute (r ≤ q ≤ k).
coh-frame : (p k : ℕ) (D : Pre (suc (suc (p + k))))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : Dom (frame p (suc (suc k)) D))
            → restr-frame p k (pre D) q Hq ε
                (restr-frame p (suc k) D r
                   (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
              ≡ restr-frame p k (pre D) r (le-trans r q k Hr Hq) ω
                  (restr-frame p (suc k) D (suc q) Hq ε d)

coh-layer : (p k : ℕ) (D : Pre (suc (suc (suc (p + k)))))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : Dom (frame p (suc (suc (suc k))) D))
            (l : Dom (layer p (suc (suc k)) D d))
            → subst (λ x → Dom (layer p k (pre (pre D)) x))
                (coh-frame p (suc k) D (suc q) Hq (suc r) Hr ε ω d)
                (restr-layer p k (pre D) q Hq ε
                   (restr-frame p (suc (suc k)) D (suc r)
                      (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                   (restr-layer p (suc k) D r
                      (le-trans r q (suc k) Hr (le-up q k Hq)) ω d l))
              ≡ restr-layer p k (pre D) r (le-trans r q k Hr Hq) ω
                  (restr-frame p (suc (suc k)) D (suc (suc q)) Hq ε d)
                  (restr-layer p (suc k) D (suc q) Hq ε d l)

coh-painting : (p k : ℕ) (D : Pre (suc (suc (p + k))))
               (E : Fil (suc (suc (p + k))) 0 D)
               (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
               (d : Dom (frame p (suc (suc k)) D))
               (c : Dom (painting p (suc (suc k)) D E d))
               → subst (λ x → Dom (painting p k (pre (pre D))
                                     (fil (pre D)) x))
                   (coh-frame p k D q Hq r Hr ε ω d)
                   (restr-painting p k (pre D) (fil D) q Hq ε
                      (restr-frame p (suc k) D r
                         (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                      (restr-painting p (suc k) D E r
                         (le-trans r q (suc k) Hr (le-up q k Hq)) ω d c))
                 ≡ restr-painting p k (pre D) (fil D) r
                     (le-trans r q k Hr Hq) ω
                     (restr-frame p (suc k) D (suc q) Hq ε d)
                     (restr-painting p (suc k) D E (suc q) Hq ε d c)

------------------------------------------------------------------------
-- The block: definitions
------------------------------------------------------------------------

{-# TERMINATING #-}
frame zero    k D = hunit
frame (suc p) k D = hΣ (frame p (suc k) D) (λ d → layer p k D d)

-- The prefix is matched, not projected: Agda's termination checker sees
-- a pattern variable as a subterm of the matched argument, and that is
-- how the level descent (`layer` at dimension p+k+1 calling `painting`
-- at p+k) enters the call matrices at all.
{-# TERMINATING #-}
layer p k (D ∷ E) d =
  hΠ arity (λ ε → painting p k D E
                    (restr-frame p k (D ∷ E) 0 tt ε d))

{-# TERMINATING #-}
painting p zero    D E d = E d
painting p (suc k) D E d =
  hΣ (layer p k D d) (λ l → painting (suc p) k D E (d , l))

{-# TERMINATING #-}
restr-frame zero    k D q Hq ε d       = tt
restr-frame (suc p) k D q Hq ε (d , l) =
  restr-frame p (suc k) D (suc q) Hq ε d ,
  restr-layer p k D q Hq ε d l

{-# TERMINATING #-}
restr-layer p k ((D ∷ E₁) ∷ E₂) q Hq ε d l ω =
  subst (λ x → Dom (painting p k D E₁ x))
    (coh-frame p k ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting p k (D ∷ E₁) E₂ q Hq ε
      (restr-frame p (suc k) ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))

restr-painting p k       (D ∷ E₁) E zero    Hq ε d (l , c) = l ε
restr-painting p zero    D        E (suc q) ()
restr-painting p (suc k) (D ∷ E₁) E (suc q) Hq ε d (l , c) =
  restr-layer p k (D ∷ E₁) q Hq ε d l ,
  restr-painting (suc p) k (D ∷ E₁) E q Hq ε (d , l) c

{-# TERMINATING #-}
coh-frame zero    k D q Hq r Hr ε ω d       = refl
coh-frame (suc p) k D q Hq r Hr ε ω (d , l) =
  Σ≡ (coh-frame p (suc k) D (suc q) Hq (suc r) Hr ε ω d)
     (coh-layer p k D q Hq r Hr ε ω d l)

-- The layer coherence: a Π-layer bridge step, then the fused
-- rew-cohLayer33 with the painting coherence and the 2-dimensional
-- frame coherence (which is free: frames are HSets) as premises.
-- Every path implicit of rew-cohLayer33 has to be given: the goal only
-- exposes them after unfolding two nested restr-layer clauses, and
-- Agda's unifier gives up there (the V1 decision-8 spots, at scale).
coh-layer p k (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω d l =
  Π-subst-ext
    {B = λ θ x → Dom (painting p k D E₁ (restr-frame p k P₁ 0 tt θ x))}
    (coh-frame p (suc k) P₃ (suc q) Hq (suc r) Hr ε ω d)
    (λ θ → rew-cohLayer33
      {P = λ x → Dom (painting p k D E₁ x)}
      {S2 = λ m → Dom (painting p (suc k) P₁ E₂ m)}
      {S3 = λ m → Dom (painting p (suc k) P₁ E₂ m)}
      {rf0 = λ x → restr-frame p k P₁ 0 tt θ x}
      {rfF = λ m → restr-frame p k P₁ q Hq ε m}
      {rfG = λ m → restr-frame p k P₁ r H₂ ω m}
      {F = λ m c → restr-painting p k P₁ E₂ q Hq ε m c}
      {G = λ m c → restr-painting p k P₁ E₂ r H₂ ω m c}
      {E1 = coh-frame p (suc k) P₃ (suc q) Hq (suc r) Hr ε ω d}
      {m1 = restr-frame p (suc k) P₂ r H₁ ω (b θ)}
      {m2 = restr-frame p (suc k) P₂ 0 tt θ dR}
      {C2 = coh-frame p (suc k) P₃ r H₁ 0 tt ω θ d}
      {n1 = restr-frame p (suc k) P₂ (suc q) Hq ε (b θ)}
      {n2 = restr-frame p (suc k) P₂ 0 tt θ dE}
      {D2 = coh-frame p (suc k) P₃ (suc q) Hq 0 tt ε θ d}
      {C1 = coh-frame p k P₂ q Hq 0 tt ε θ dR}
      {D1 = coh-frame p k P₂ r H₂ 0 tt ω θ dE}
      {K = coh-frame p k P₂ q Hq r Hr ε ω (b θ)}
      {aL = restr-painting p (suc k) P₂ E₃ r H₁ ω (b θ) (l θ)}
      {aR = restr-painting p (suc k) P₂ E₃ (suc q) Hq ε (b θ) (l θ)}
      (coh-painting p k P₂ E₃ q Hq r Hr ε ω (b θ) (l θ))
      (isSetDom (frame p k D) _ _ _ _))
  where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  -- the ω-restriction of d used by the outer restr-layer on each side,
  dR = restr-frame p (suc (suc k)) P₃ (suc r) H₁ ω d
  dE = restr-frame p (suc (suc k)) P₃ (suc (suc q)) Hq ε d
  -- and its θ-restriction, where the painting coherence applies.
  b : (θ : arity) → Dom (frame p (suc (suc k)) P₂)
  b θ = restr-frame p (suc (suc k)) P₃ 0 tt θ d

-- The painting coherence.  With Π-layers the r = 0 case is refl; the
-- r , q ≥ 1 case is a dependent Σ-path whose base is the very clause
-- coh-frame unfolds to, so the alignment holds by clause unfolding
-- rather than by a stored-term discipline.
-- Without eta on the prefix the r = 0 reduction (`restr-painting … 0`
-- ↦ `l ω`) fires only when the prefix is a constructor, so this
-- clause has to match it even though the proof does not use it.
coh-painting p k ((D ∷ E₁) ∷ E₂) E q Hq zero Hr ε ω d (l , c) = refl
coh-painting p k       D          E zero    Hq (suc r) ()
coh-painting p zero    D          E (suc q) ()
coh-painting p (suc k) ((D ∷ E₁) ∷ E₂) E (suc q) Hq (suc r) Hr ε ω d (l , c) =
  Σ≡dep {P = λ x → Dom (layer p k D x)}
        {Q = λ z → Dom (painting (suc p) k D E₁ z)}
    (coh-frame p (suc k) ((D ∷ E₁) ∷ E₂) (suc q) Hq (suc r) Hr ε ω d)
    (coh-layer p k ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω d l)
    (coh-painting (suc p) k ((D ∷ E₁) ∷ E₂) E q Hq r Hr ε ω (d , l) c)

------------------------------------------------------------------------
-- The tower
------------------------------------------------------------------------

-- The full frame at dimension n: the one whose index is the length.
fullframe : {n : ℕ} (D : Pre n) → HSet₀
fullframe {n} D = frame n 0 D

record νSet→ (n : ℕ) (D : Pre n) : Set₁ where
  coinductive
  constructor _∷ν_
  field
    this : Fil n 0 D
    next : νSet→ (suc n) (D ∷ this)
open νSet→ public

νSets : Set₁
νSets = νSet→ 0 tt*
