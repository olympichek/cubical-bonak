------------------------------------------------------------------------
-- Bonak.νGpd — the νGpd tower: the groupoid storey of Bonak.νSet, on
-- the same storage, index, fuel and equality disciplines (see that
-- file's header; everything said there carries over verbatim).
--
-- What changes at the groupoid level:
--
--   * Frames, layers and paintings are HGpds (gunit / gΣ / gΠ).
--   * The layer coherence can no longer close by square filling in an
--     HSet of frames: the square it needs — the three-face hexagon in
--     Square form — becomes the stored-by-computation 2-coherence
--     `coh2-frame`, and the mutual block grows one more storey:
--     coh2-frame / coh2-layer / coh2-painting, shaped exactly like
--     coh-frame / coh-layer / coh-painting one level up, with squares
--     for paths and dependent squares for dependent paths.
--   * The s = 0 painting 2-coherence is the FILLER of the layer
--     coherence's square composition (Bonak.GpdLemmas' cohLayer-fillP),
--     exactly as the r = 0 painting coherence is subst-filler of
--     restr-layer's transport one storey down.
--   * The only truncation site is isGroupoid→Cube inside coh2-layer:
--     the four-face permutahedron cube in the HGpd of frames, the
--     cubical form of Rocq's single GUIP use (νGpd.v:918).
--   * Termination stays checked, no pragma: the coh2 statements write
--     occurrences up to suc⁴ of the member's fuel (coh2-layer's
--     premise pack lives four storeys up), so the call matrices carry
--     +4 increases and the checker needs --termination-depth=4 —
--     rejected at 3 on the restr-frame..coh2-layer-suc group, exactly
--     as Bonak.νSet's +3 statements need depth 3.
------------------------------------------------------------------------

{-# OPTIONS --rewriting --termination-depth=4 #-}

module Bonak.νGpd (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.EqProp
open import Bonak.RewLemmas
open import Bonak.GpdLemmas
open import Bonak.NatRew

HGpd₀ : Set₁
HGpd₀ = HGpd lzero

-- The prefix's cons cell, as in Bonak.νSet.
record Snoc (A : Set₁) (B : A → Set₁) : Set₁ where
  no-eta-equality; pattern
  constructor _∷_
  field
    pre : A
    fil : B pre
open Snoc public

------------------------------------------------------------------------
-- The block: signatures
------------------------------------------------------------------------

-- The prefix of fillers, and the filler over one.
Pre : ℕ → Set₁
Fil : (p k : ℕ) (D : Pre (p + k)) → Set₁

Pre zero    = Unit*
Pre (suc n) = Snoc (Pre n) (Fil n 0)

-- frame(p) at dimension p + k, at fuel n ~ p + k.
frame : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k)) → HGpd₀

-- A filler eats a point of the full frame AT ANY FUEL.
Fil p k D = (m : ℕ) .(f : EqN m (p + k)) → GDom (frame m p k f D) → HGpd₀

-- layer(p) at dimension p + k + 1; its fuel is its point's.
layer : (n p k : ℕ) .(e : EqN n (suc (p + k))) (D : Pre (suc (p + k)))
        (d : GDom (frame n p (suc k) e D)) → HGpd₀

-- painting(p) at dimension p + k, over the filler E.
painting : (n p k : ℕ) .(e : EqN n (p + k)) (D : Pre (p + k))
           (E : Fil (p + k) 0 D)
           (d : GDom (frame n p k e D)) → HGpd₀

-- The three restrictions: dimension p + k + 1 ↦ dimension p + k along
-- the q-th face (q ≤ k); the fuel is the OUTPUT's, the input's is
-- suc of it.
restr-frame : (n p k : ℕ) .(e : EqN n (p + k))
              (D : Pre (suc (p + k)))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : GDom (frame (suc n) p (suc k) e D))
              → GDom (frame n p k e (pre D))

restr-layer : (n p k : ℕ) .(e : EqN n (suc (p + k)))
              (D : Pre (suc (suc (p + k))))
              (q : ℕ) .(Hq : q ≤ k) (ε : arity)
              (d : GDom (frame (suc n) p (suc (suc k)) e D))
              (l : GDom (layer (suc n) p (suc k) e D d))
              → GDom (layer n p k e (pre D)
                        (restr-frame n p (suc k) e D (suc q) Hq ε d))

restr-painting : (n p k : ℕ) .(e : EqN n (p + k))
                 (D : Pre (suc (p + k))) (E : Fil (suc (p + k)) 0 D)
                 (q : ℕ) .(Hq : q ≤ k) (ε : arity)
                 (d : GDom (frame (suc n) p (suc k) e D))
                 (c : GDom (painting (suc n) p (suc k) e D E d))
                 → GDom (painting n p k e (pre D) (fil D)
                           (restr-frame n p k e D q Hq ε d))

-- The three coherences: the faces q and r commute (r ≤ q ≤ k); the
-- fuel is the final output's, two below the point's.
coh-frame : (n p k : ℕ) .(e : EqN n (p + k))
            (D : Pre (suc (suc (p + k))))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : GDom (frame (suc (suc n)) p (suc (suc k)) e D))
            → restr-frame n p k e (pre D) q Hq ε
                (restr-frame (suc n) p (suc k) e D r
                   (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
              ≡ restr-frame n p k e (pre D) r (le-trans r q k Hr Hq) ω
                  (restr-frame (suc n) p (suc k) e D (suc q) Hq ε d)

coh-layer : (n p k : ℕ) .(e : EqN n (suc (p + k)))
            (D : Pre (suc (suc (suc (p + k)))))
            (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q) (ε ω : arity)
            (d : GDom (frame (suc (suc n)) p (suc (suc (suc k))) e D))
            (l : GDom (layer (suc (suc n)) p (suc (suc k)) e D d))
            → PathP (λ i → GDom (layer n p k e (pre (pre D))
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
               (d : GDom (frame (suc (suc n)) p (suc (suc k)) e D))
               (c : GDom (painting (suc (suc n)) p (suc (suc k)) e D E d))
               → PathP (λ i → GDom (painting n p k e (pre (pre D))
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

-- The three 2-coherences: the faces q, r and s commute (s ≤ r ≤ q ≤ k);
-- the fuel is the final output's, three below the point's.  The
-- 2-dimensional frame coherence is the three-face hexagon in Square
-- form — the square coh-layer's proof consumes, with the s-th face
-- generalized from the layer direction (s = 0) to any s ≤ r: the
-- coherence at the s-restricted point connects, along the s-restriction
-- of the one-level-up coherence, the two conjugation composites.
coh2-frame : (n p k : ℕ) .(e : EqN n (p + k))
             (D : Pre (suc (suc (suc (p + k)))))
             (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
             (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
             (d : GDom (frame (suc (suc (suc n))) p (suc (suc (suc k)))
                          e D))
             → Square
                 (coh-frame n p k e (pre D) q Hq r Hr ε ω
                    (restr-frame (suc (suc n)) p (suc (suc k)) e D s
                       (le-up s (suc k) (le-up s k
                          (le-trans s r k Hs (le-trans r q k Hr Hq))))
                       θ d))
                 (cong (restr-frame n p k e (pre (pre D)) s
                          (le-trans s r k Hs (le-trans r q k Hr Hq)) θ)
                    (coh-frame (suc n) p (suc k) e D
                       (suc q) Hq (suc r) Hr ε ω d))
                 (cong (restr-frame n p k e (pre (pre D)) q Hq ε)
                    (coh-frame (suc n) p (suc k) e D r
                       (le-trans r q (suc k) Hr (le-up q k Hq)) s Hs
                       ω θ d)
                  ∙ coh-frame n p k e (pre D) q Hq s
                      (le-trans s r q Hs Hr) ε θ
                      (restr-frame (suc (suc n)) p (suc (suc k)) e D
                         (suc r) (le-trans r q (suc k) Hr (le-up q k Hq))
                         ω d))
                 (cong (restr-frame n p k e (pre (pre D)) r
                          (le-trans r q k Hr Hq) ω)
                    (coh-frame (suc n) p (suc k) e D (suc q) Hq s
                       (le-up s q (le-trans s r q Hs Hr)) ε θ d)
                  ∙ coh-frame n p k e (pre D) r (le-trans r q k Hr Hq)
                      s Hs ω θ
                      (restr-frame (suc (suc n)) p (suc (suc k)) e D
                         (suc (suc q)) Hq ε d))

coh2-layer : (n p k : ℕ) .(e : EqN n (suc (p + k)))
             (D : Pre (suc (suc (suc (suc (p + k))))))
             (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
             (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
             (d : GDom (frame (suc (suc (suc n))) p
                          (suc (suc (suc (suc k)))) e D))
             (l : GDom (layer (suc (suc (suc n))) p (suc (suc (suc k)))
                          e D d))
             → SquareP
                 (λ i j → GDom (layer n p k e (pre (pre (pre D)))
                    (coh2-frame n p (suc k) e D (suc q) Hq (suc r) Hr
                       (suc s) Hs ε ω θ d i j)))
                 (coh-layer n p k e (pre D) q Hq r Hr ε ω
                    (restr-frame (suc (suc n)) p (suc (suc (suc k))) e D
                       (suc s)
                       (le-up s (suc k) (le-up s k
                          (le-trans s r k Hs (le-trans r q k Hr Hq))))
                       θ d)
                    (restr-layer (suc (suc n)) p (suc (suc k)) e D s
                       (le-up s (suc k) (le-up s k
                          (le-trans s r k Hs (le-trans r q k Hr Hq))))
                       θ d l))
                 (λ i → restr-layer n p k e (pre (pre D)) s
                          (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
                          (coh-frame (suc n) p (suc (suc k)) e D
                             (suc (suc q)) Hq (suc (suc r)) Hr ε ω d i)
                          (coh-layer (suc n) p (suc k) e D
                             (suc q) Hq (suc r) Hr ε ω d l i))
                 (compPathP
                    {P = λ x → GDom (layer n p k e (pre (pre (pre D)))
                                       x)}
                    (λ i → restr-layer n p k e (pre (pre D)) q Hq ε
                             (coh-frame (suc n) p (suc (suc k)) e D
                                (suc r)
                                (le-trans r q (suc k) Hr (le-up q k Hq))
                                (suc s) Hs ω θ d i)
                             (coh-layer (suc n) p (suc k) e D r
                                (le-trans r q (suc k) Hr (le-up q k Hq))
                                s Hs ω θ d l i))
                    (coh-layer n p k e (pre D) q Hq s
                       (le-trans s r q Hs Hr) ε θ
                       (restr-frame (suc (suc n)) p (suc (suc (suc k)))
                          e D (suc (suc r))
                          (le-trans r q (suc k) Hr (le-up q k Hq)) ω d)
                       (restr-layer (suc (suc n)) p (suc (suc k)) e D
                          (suc r)
                          (le-trans r q (suc k) Hr (le-up q k Hq)) ω
                          d l)))
                 (compPathP
                    {P = λ x → GDom (layer n p k e (pre (pre (pre D)))
                                       x)}
                    (λ i → restr-layer n p k e (pre (pre D)) r
                             (le-trans r q k Hr Hq) ω
                             (coh-frame (suc n) p (suc (suc k)) e D
                                (suc (suc q)) Hq (suc s)
                                (le-up s q (le-trans s r q Hs Hr)) ε θ
                                d i)
                             (coh-layer (suc n) p (suc k) e D (suc q) Hq
                                s (le-up s q (le-trans s r q Hs Hr))
                                ε θ d l i))
                    (coh-layer n p k e (pre D) r (le-trans r q k Hr Hq)
                       s Hs ω θ
                       (restr-frame (suc (suc n)) p (suc (suc (suc k)))
                          e D (suc (suc (suc q))) Hq ε d)
                       (restr-layer (suc (suc n)) p (suc (suc k)) e D
                          (suc (suc q)) Hq ε d l)))

-- The recursive layer 2-coherence at a fixed point of the arity: the
-- (i , j)-square of the goal's θ'-applied faces.  A separate member so
-- that the interval directions are λ-bound rather than clause
-- patterns: the giant body is then checked against its boundary once,
-- by the path-abstraction rule, and coh2-layer's own clause is a
-- one-application body whose boundary matches syntactically (interval
-- clause patterns additionally trigger the checker's boundary-
-- confluence pass, which normalizes and reifies the clause body per
-- face — prohibitive at this term size).
Coh2LayerSucT : (n p k : ℕ) .(e : EqN (suc n) (suc (p + k)))
                 (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E₃ : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂))
                 (E₄ : Fil (suc (suc (suc (p + k)))) 0
                         (((D ∷ E₁) ∷ E₂) ∷ E₃))
                 (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
                 (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
                 (d : GDom (frame (suc (suc (suc (suc n)))) p
                              (suc (suc (suc (suc k)))) e
                              ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)))
                 (l : GDom (layer (suc (suc (suc (suc n)))) p
                              (suc (suc (suc k)))
                              e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) d))
                 (θ' : arity)
                 → Set
coh2-layer-suc : (n p k : ℕ) .(e : EqN (suc n) (suc (p + k)))
                 (D : Pre (p + k)) (E₁ : Fil (p + k) 0 D)
                 (E₂ : Fil (suc (p + k)) 0 (D ∷ E₁))
                 (E₃ : Fil (suc (suc (p + k))) 0 ((D ∷ E₁) ∷ E₂))
                 (E₄ : Fil (suc (suc (suc (p + k)))) 0
                         (((D ∷ E₁) ∷ E₂) ∷ E₃))
                 (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
                 (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
                 (d : GDom (frame (suc (suc (suc (suc n)))) p
                              (suc (suc (suc (suc k)))) e
                              ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)))
                 (l : GDom (layer (suc (suc (suc (suc n)))) p
                              (suc (suc (suc k)))
                              e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) d))
                 (θ' : arity)
                 → Coh2LayerSucT n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs
                     ε ω θ d l θ'

coh2-painting : (n p k : ℕ) .(e : EqN n (p + k))
                (D : Pre (suc (suc (suc (p + k)))))
                (E : Fil (suc (suc (suc (p + k)))) 0 D)
                (q : ℕ) .(Hq : q ≤ k) (r : ℕ) .(Hr : r ≤ q)
                (s : ℕ) .(Hs : s ≤ r) (ε ω θ : arity)
                (d : GDom (frame (suc (suc (suc n))) p
                             (suc (suc (suc k))) e D))
                (c : GDom (painting (suc (suc (suc n))) p
                             (suc (suc (suc k))) e D E d))
                → SquareP
                    (λ i j → GDom (painting n p k e (pre (pre (pre D)))
                       (fil (pre (pre D)))
                       (coh2-frame n p k e D q Hq r Hr s Hs ε ω θ d
                          i j)))
                    (coh-painting n p k e (pre D) (fil D) q Hq r Hr ε ω
                       (restr-frame (suc (suc n)) p (suc (suc k)) e D s
                          (le-up s (suc k) (le-up s k
                             (le-trans s r k Hs (le-trans r q k Hr Hq))))
                          θ d)
                       (restr-painting (suc (suc n)) p (suc (suc k)) e D
                          E s
                          (le-up s (suc k) (le-up s k
                             (le-trans s r k Hs (le-trans r q k Hr Hq))))
                          θ d c))
                    (λ i → restr-painting n p k e (pre (pre D))
                             (fil (pre D)) s
                             (le-trans s r k Hs (le-trans r q k Hr Hq))
                             θ
                             (coh-frame (suc n) p (suc k) e D (suc q) Hq
                                (suc r) Hr ε ω d i)
                             (coh-painting (suc n) p (suc k) e D E
                                (suc q) Hq (suc r) Hr ε ω d c i))
                    (compPathP
                       {P = λ x → GDom (painting n p k e
                              (pre (pre (pre D))) (fil (pre (pre D)))
                              x)}
                       (λ i → restr-painting n p k e (pre (pre D))
                                (fil (pre D)) q Hq ε
                                (coh-frame (suc n) p (suc k) e D r
                                   (le-trans r q (suc k) Hr
                                      (le-up q k Hq))
                                   s Hs ω θ d i)
                                (coh-painting (suc n) p (suc k) e D E r
                                   (le-trans r q (suc k) Hr
                                      (le-up q k Hq))
                                   s Hs ω θ d c i))
                       (coh-painting n p k e (pre D) (fil D) q Hq s
                          (le-trans s r q Hs Hr) ε θ
                          (restr-frame (suc (suc n)) p (suc (suc k)) e D
                             (suc r)
                             (le-trans r q (suc k) Hr (le-up q k Hq))
                             ω d)
                          (restr-painting (suc (suc n)) p (suc (suc k))
                             e D E (suc r)
                             (le-trans r q (suc k) Hr (le-up q k Hq))
                             ω d c)))
                    (compPathP
                       {P = λ x → GDom (painting n p k e
                              (pre (pre (pre D))) (fil (pre (pre D)))
                              x)}
                       (λ i → restr-painting n p k e (pre (pre D))
                                (fil (pre D)) r (le-trans r q k Hr Hq) ω
                                (coh-frame (suc n) p (suc k) e D (suc q)
                                   Hq s
                                   (le-up s q (le-trans s r q Hs Hr))
                                   ε θ d i)
                                (coh-painting (suc n) p (suc k) e D E
                                   (suc q) Hq s
                                   (le-up s q (le-trans s r q Hs Hr))
                                   ε θ d c i))
                       (coh-painting n p k e (pre D) (fil D) r
                          (le-trans r q k Hr Hq) s Hs ω θ
                          (restr-frame (suc (suc n)) p (suc (suc k)) e D
                             (suc (suc q)) Hq ε d)
                          (restr-painting (suc (suc n)) p (suc (suc k))
                             e D E (suc (suc q)) Hq ε d c)))

------------------------------------------------------------------------
-- The block: definitions
------------------------------------------------------------------------

frame n zero    k e D = gunit
frame n (suc p) k e D =
  gΣ (frame n p (suc k) e D) (λ d → layer n p k e D d)

layer zero    p k ()
layer (suc n) p k e (D ∷ E) d =
  gΠ arity (λ ε → painting n p k e D E
                    (restr-frame n p k e (D ∷ E) 0 tt ε d))

painting n p zero    e D E d = E n e d
painting n p (suc k) e D E d =
  gΣ (layer n p k e D d) (λ l → painting n (suc p) k e D E (d , l))

restr-frame n zero    k e D q Hq ε d       = tt
restr-frame n (suc p) k e D q Hq ε (d , l) =
  restr-frame n p (suc k) e D (suc q) Hq ε d ,
  restr-layer n p k e D q Hq ε d l

restr-layer zero    p k ()
restr-layer (suc n) p k e ((D ∷ E₁) ∷ E₂) q Hq ε d l ω =
  subst (λ x → GDom (painting n p k e D E₁ x))
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

-- The layer coherence.  As in Bonak.νSet, except that the closing
-- square — free there because frames are HSets — is here the s = 0
-- instance of the 2-dimensional frame coherence.
coh-layer zero    p k ()
coh-layer (suc n) p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω d l i θ =
  cohLayer-squareP
    {P = λ x → GDom (painting n p k e D E₁ x)}
    {S2 = λ m → GDom (painting (suc n) p (suc k) e P₁ E₂ m)}
    {S3 = λ m → GDom (painting (suc n) p (suc k) e P₁ E₂ m)}
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
    (coh2-frame n p k e P₃ q Hq r Hr 0 tt ε ω θ d)
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
  b : (θ : arity) → GDom (frame (suc (suc n)) p (suc (suc k)) e P₂)
  b θ = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ 0 tt θ d

-- The painting coherence: as in Bonak.νSet.
coh-painting n p k e ((D ∷ E₁) ∷ E₂) E q Hq zero Hr ε ω d (l , c) =
  subst-filler (λ x → GDom (painting n p k e D E₁ x))
    (coh-frame n p k e ((D ∷ E₁) ∷ E₂) q Hq 0 tt ε ω d)
    (restr-painting n p k e (D ∷ E₁) E₂ q Hq ε
      (restr-frame (suc n) p (suc k) e ((D ∷ E₁) ∷ E₂) 0 tt ω d) (l ω))
coh-painting n p k e       D          E zero    Hq (suc r) ()
coh-painting n p zero    e D        E (suc q) ()
coh-painting n p (suc k) e ((D ∷ E₁) ∷ E₂) E (suc q) Hq (suc r) Hr ε ω
             d (l , c) i =
  coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω d l i ,
  coh-painting n (suc p) k e ((D ∷ E₁) ∷ E₂) E q Hq r Hr ε ω (d , l) c i

-- The frame 2-coherence.  At suc p the single-cell faces and the
-- interior pair componentwise; the two composite faces are assembled
-- by the decomposition lemma Σ≡hex.hex from the square of first
-- components and the layer 2-coherence over it.
coh2-frame n zero    k e D q Hq r Hr s Hs ε ω θ d = λ _ _ → tt
coh2-frame n (suc p) k e D q Hq r Hr s Hs ε ω θ (d , l) i j =
  Σ≡hex.hex
    (λ i' → restr-frame n p (suc k) e (pre (pre D)) (suc q) Hq ε
              (C2f i'))
    (coh-frame n p (suc k) e (pre D) (suc q) Hq (suc s) HsHr ε θ dR)
    (λ i' → restr-layer n p k e (pre (pre D)) q Hq ε (C2f i') (C2s i'))
    (coh-layer n p k e (pre D) q Hq s HsHr ε θ dR dRl)
    (λ i' → restr-frame n p (suc k) e (pre (pre D)) (suc r) H₂ ω
              (D2f i'))
    (coh-frame n p (suc k) e (pre D) (suc r) H₂ (suc s) Hs ω θ dE)
    (λ i' → restr-layer n p k e (pre (pre D)) r H₂ ω (D2f i') (D2s i'))
    (coh-layer n p k e (pre D) r H₂ s Hs ω θ dE dEl)
    (coh-frame n p (suc k) e (pre D) (suc q) Hq (suc r) Hr ε ω dSf)
    (coh-layer n p k e (pre D) q Hq r Hr ε ω dSf dSl)
    (λ i' → restr-frame n p (suc k) e (pre (pre D)) (suc s) HsB θ
              (E1f i'))
    (λ i' → restr-layer n p k e (pre (pre D)) s HsB θ (E1f i')
              (E1s i'))
    (coh2-frame n p (suc k) e D (suc q) Hq (suc r) Hr (suc s) Hs ε ω θ
       d)
    (coh2-layer n p k e D q Hq r Hr s Hs ε ω θ d l)
    i j
  where
  H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  HsHr = le-trans s r q Hs Hr
  Hs↑ = le-up s q (le-trans s r q Hs Hr)
  HsB = le-trans s r k Hs (le-trans r q k Hr Hq)
  HsS = le-up s (suc k) (le-up s k HsB)
  C2f = coh-frame (suc n) p (suc (suc k)) e D (suc r) H₁ (suc s) Hs
          ω θ d
  C2s = coh-layer (suc n) p (suc k) e D r H₁ s Hs ω θ d l
  D2f = coh-frame (suc n) p (suc (suc k)) e D (suc (suc q)) Hq (suc s)
          Hs↑ ε θ d
  D2s = coh-layer (suc n) p (suc k) e D (suc q) Hq s Hs↑ ε θ d l
  E1f = coh-frame (suc n) p (suc (suc k)) e D (suc (suc q)) Hq
          (suc (suc r)) Hr ε ω d
  E1s = coh-layer (suc n) p (suc k) e D (suc q) Hq (suc r) Hr ε ω d l
  dR = restr-frame (suc (suc n)) p (suc (suc (suc k))) e D (suc (suc r))
         H₁ ω d
  dRl = restr-layer (suc (suc n)) p (suc (suc k)) e D (suc r) H₁ ω d l
  dE = restr-frame (suc (suc n)) p (suc (suc (suc k))) e D
         (suc (suc (suc q))) Hq ε d
  dEl = restr-layer (suc (suc n)) p (suc (suc k)) e D (suc (suc q)) Hq
          ε d l
  dSf = restr-frame (suc (suc n)) p (suc (suc (suc k))) e D (suc s) HsS
          θ d
  dSl = restr-layer (suc (suc n)) p (suc (suc k)) e D s HsS θ d l

-- The layer 2-coherence: the four-face permutahedron.  Pointwise in
-- θ', the goal square is the coh2-painting premise at the
-- θ'-restricted point, transported over the isGroupoid→Cube interior
-- (the storey's one truncation site) along four lateral squares:
-- each is the vertical composite of a conjugation square — the
-- premise's face carried along the r = 0 frame coherence κ by
-- application — with the canonical filler of the corresponding goal
-- face (cohLayer-fillP for the coherence faces, subst-filler for the
-- transport face), the composite faces joined pointwise by ∙sliceP
-- and their junction edges aligned by cong²Funct + assocP cells.
-- The goal's composite faces are Π-valued composites applied at θ',
-- and comp in a Π-type evaluates through the function direction, so
-- the cube is built with the pointwise composites as faces and
-- coh2Layer-cubeP carries it — base and fiber together — along the
-- ∙Πapp cells to the goal's applied composites.
Coh2LayerSucT n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ' =
  SquareP
    (λ i j → GDom (painting n p k e D E₁
       (restr-frame n p k e (D ∷ E₁) 0 tt θ'
          (coh2-frame (suc n) p (suc k) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
             (suc q) Hq (suc r) Hr (suc s) Hs ε ω θ d
             i j))))
    (λ j → coh-layer (suc n) p k e
             (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr ε ω
             (restr-frame (suc (suc (suc n))) p
                (suc (suc (suc k))) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                (suc s)
                (le-up s (suc k) (le-up s k
                   (le-trans s r k Hs
                      (le-trans r q k Hr Hq))))
                θ d)
             (restr-layer (suc (suc (suc n))) p
                (suc (suc k)) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) s
                (le-up s (suc k) (le-up s k
                   (le-trans s r k Hs
                      (le-trans r q k Hr Hq))))
                θ d l)
             j θ')
    (λ j → restr-layer (suc n) p k e ((D ∷ E₁) ∷ E₂) s
             (le-trans s r k Hs (le-trans r q k Hr Hq)) θ
             (coh-frame (suc (suc n)) p (suc (suc k)) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                (suc (suc q)) Hq (suc (suc r)) Hr ε ω d
                j)
             (coh-layer (suc (suc n)) p (suc k) e
                ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                (suc q) Hq (suc r) Hr ε ω d l j)
             θ')
    (λ i → compPathP
       {P = λ x → GDom (layer (suc n) p k e (D ∷ E₁)
                          x)}
       (λ i' → restr-layer (suc n) p k e
                 ((D ∷ E₁) ∷ E₂) q Hq ε
                 (coh-frame (suc (suc n)) p (suc (suc k))
                    e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                    (suc r)
                    (le-trans r q (suc k) Hr
                       (le-up q k Hq))
                    (suc s) Hs ω θ d i')
                 (coh-layer (suc (suc n)) p (suc k) e
                    ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) r
                    (le-trans r q (suc k) Hr
                       (le-up q k Hq))
                    s Hs ω θ d l i'))
       (coh-layer (suc n) p k e
          (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq s
          (le-trans s r q Hs Hr) ε θ
          (restr-frame (suc (suc (suc n))) p
             (suc (suc (suc k))) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
             (suc (suc r))
             (le-trans r q (suc k) Hr (le-up q k Hq))
             ω d)
          (restr-layer (suc (suc (suc n))) p
             (suc (suc k)) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) (suc r)
             (le-trans r q (suc k) Hr (le-up q k Hq))
             ω d l))
       i θ')
    (λ i → compPathP
       {P = λ x → GDom (layer (suc n) p k e (D ∷ E₁)
                          x)}
       (λ i' → restr-layer (suc n) p k e
                 ((D ∷ E₁) ∷ E₂) r
                 (le-trans r q k Hr Hq) ω
                 (coh-frame (suc (suc n)) p (suc (suc k))
                    e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                    (suc (suc q)) Hq (suc s)
                    (le-up s q (le-trans s r q Hs Hr))
                    ε θ d i')
                 (coh-layer (suc (suc n)) p (suc k) e
                    ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
                    (suc q) Hq s
                    (le-up s q (le-trans s r q Hs Hr))
                    ε θ d l i'))
       (coh-layer (suc n) p k e
          (((D ∷ E₁) ∷ E₂) ∷ E₃) r
          (le-trans r q k Hr Hq) s Hs ω θ
          (restr-frame (suc (suc (suc n))) p
             (suc (suc (suc k))) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
             (suc (suc (suc q))) Hq ε d)
          (restr-layer (suc (suc (suc n))) p
             (suc (suc k)) e
             ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
             (suc (suc q)) Hq ε d l))
       i θ')

coh2-layer zero    p k ()
coh2-layer (suc n) p k e ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄) q Hq r Hr s Hs
           ε ω θ d l i j θ' =
  coh2-layer-suc n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ' i j

coh2-layer-suc n p k e D E₁ E₂ E₃ E₄ q Hq r Hr s Hs ε ω θ d l θ' =
  coh2Layer-cubeP
       {X = GDom (frame n p k e D)} {P = P'}
       {Y = GDom (frame (suc n) p (suc k) e P₁)} {S = S'}
       {Z = GDom (frame (suc (suc n)) p (suc (suc k)) e P₂)} {T̃ = S̃}
       {T = arity}
       (isGroupoidDom (frame n p k e D)) Rθ θ'
       rfq rfr rfs Fq Fr Fs
       w⁺ r̂fr r̂fs r̂fsq r̂fsr r̂ss F̂r Ĝs F̂sq F̂sr
       (λ z → coh-frame n p k e P₂ q Hq 0 tt ε θ' z)
       (λ z → coh-frame n p k e P₂ r H₂ 0 tt ω θ' z)
       (λ z → coh-frame n p k e P₂ s HsB 0 tt θ θ' z)
       (λ z → coh-frame n p k e P₂ q Hq r Hr ε ω z)
       (λ z c → coh-painting n p k e P₂ E₃ q Hq r Hr ε ω z c)
       (λ z → coh-frame n p k e P₂ q Hq s HsHr ε θ z)
       (λ z c → coh-painting n p k e P₂ E₃ q Hq s HsHr ε θ z c)
       (λ z → coh-frame n p k e P₂ r H₂ s Hs ω θ z)
       (λ z c → coh-painting n p k e P₂ E₃ r H₂ s Hs ω θ z c)
       κ' cS̃ κ'C c̃C κ'E c̃E
       C2f' D2f' E1f'
       C2K D2K sC sD D2C D1E1
       (coh-frame (suc n) p (suc k) e P₃ r H₁ s Hs ω θ b')
       (coh-frame (suc n) p (suc k) e P₃ (suc q) Hq s Hs↑ ε θ b')
       (coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc r) Hr ε ω b')
       E1K
       (coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc s) HsHr ε θ
          dRf')
       (coh-frame (suc n) p (suc k) e P₃ (suc r)
          (le-trans (suc r) (suc q) (suc k) Hr Hq) (suc s) Hs ω θ dEf')
       (coh-painting (suc n) p (suc k) e P₃ E₄ r H₁ s Hs ω θ b'
          (l θ'))
       (coh-painting (suc n) p (suc k) e P₃ E₄ (suc q) Hq s Hs↑ ε θ b'
          (l θ'))
       (coh-painting (suc n) p (suc k) e P₃ E₄ (suc q) Hq (suc r) Hr
          ε ω b' (l θ'))
       sqK sqE1 sqC2' sqD2' sqC sqD
       fillK fillPE1 fillPC2s' fillPD2s' fillC fillD
       B₀
       (coh2-painting n p k e P₃ E₄ q Hq r Hr s Hs ε ω θ b' (l θ'))
       (λ ii jj → w (E2 ii jj))
       (λ o ii → ΠC.csq (~ o) ii)
       (λ o ii → ΠD.csq (~ o) ii)
       (λ o ii → ΠC.csqP (~ o) ii)
       (λ o ii → ΠD.csqP (~ o) ii)
  where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  P₄ = ((((D ∷ E₁) ∷ E₂) ∷ E₃) ∷ E₄)
  H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  HsHr = le-trans s r q Hs Hr
  HsB = le-trans s r k Hs H₂
  HsS = le-up s (suc k) (le-up s k HsB)
  -- families and restriction maps
  P' : GDom (frame n p k e D) → Set
  P' = λ x → GDom (painting n p k e D E₁ x)
  S' : GDom (frame (suc n) p (suc k) e P₁) → Set
  S' = λ y → GDom (painting (suc n) p (suc k) e P₁ E₂ y)
  S̃ : GDom (frame (suc (suc n)) p (suc (suc k)) e P₂) → Set
  S̃ = λ z → GDom (painting (suc (suc n)) p (suc (suc k)) e P₂ E₃ z)
  w = λ y → restr-frame n p k e P₁ 0 tt θ' y
  rfq = λ y → restr-frame n p k e P₁ q Hq ε y
  rfr = λ y → restr-frame n p k e P₁ r H₂ ω y
  rfs = λ y → restr-frame n p k e P₁ s HsB θ y
  Fq = λ y c → restr-painting n p k e P₁ E₂ q Hq ε y c
  Fr = λ y c → restr-painting n p k e P₁ E₂ r H₂ ω y c
  Fs = λ y c → restr-painting n p k e P₁ E₂ s HsB θ y c
  w⁺ = λ z → restr-frame (suc n) p (suc k) e P₂ 0 tt θ' z
  -- the premise's base square and the goal's
  b' = restr-frame (suc (suc (suc n))) p (suc (suc (suc k))) e P₄ 0 tt
         θ' d
  B₀ = coh2-frame n p k e P₃ q Hq r Hr s Hs ε ω θ b'
  E2 = coh2-frame (suc n) p (suc k) e P₄ (suc q) Hq (suc r) Hr (suc s)
         Hs ε ω θ d
  -- the K face: pack, filler, conjugation
  dSf = restr-frame (suc (suc (suc n))) p (suc (suc (suc k))) e P₄
          (suc s) HsS θ d
  dSl = restr-layer (suc (suc (suc n))) p (suc (suc k)) e P₄ s HsS θ d l
  bK = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ 0 tt θ' dSf
  E1K = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc r) Hr ε ω dSf
  C2K = coh-frame (suc n) p (suc k) e P₃ r H₁ 0 tt ω θ' dSf
  D2K = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq 0 tt ε θ' dSf
  dRK = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc r) H₁ ω dSf
  dEK = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc (suc q)) Hq
          ε dSf
  C1K = coh-frame n p k e P₂ q Hq 0 tt ε θ' dRK
  D1K = coh-frame n p k e P₂ r H₂ 0 tt ω θ' dEK
  KK = coh-frame n p k e P₂ q Hq r Hr ε ω bK
  m1K = restr-frame (suc n) p (suc k) e P₂ r H₁ ω bK
  m2K = restr-frame (suc n) p (suc k) e P₂ 0 tt θ' dRK
  n1K = restr-frame (suc n) p (suc k) e P₂ (suc q) Hq ε bK
  n2K = restr-frame (suc n) p (suc k) e P₂ 0 tt θ' dEK
  aLK = restr-painting (suc n) p (suc k) e P₂ E₃ r H₁ ω bK (dSl θ')
  aRK = restr-painting (suc n) p (suc k) e P₂ E₃ (suc q) Hq ε bK
          (dSl θ')
  HCPK = coh-painting n p k e P₂ E₃ q Hq r Hr ε ω bK (dSl θ')
  sqK = coh2-frame n p k e P₃ q Hq r Hr 0 tt ε ω θ' dSf
  fillK = cohLayer-fillP {P = P'} {S2 = S'} {S3 = S'} {rf0 = w}
    {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr} {E1 = E1K}
    {m1 = m1K} {m2 = m2K} {C2 = C2K} {n1 = n1K} {n2 = n2K} {D2 = D2K}
    {C1 = C1K} {D1 = D1K} {K = KK} {aL = aLK} {aR = aRK} HCPK sqK
  κ' = coh-frame (suc (suc n)) p (suc (suc k)) e P₄ s HsS 0 tt θ θ' d
  cS̃ = restr-painting (suc (suc n)) p (suc (suc k)) e P₃ E₄ s HsS θ b'
         (l θ')
  -- the E1 face: conjugation and transport filler
  E1f' = coh-frame (suc (suc n)) p (suc (suc k)) e P₄ (suc (suc q)) Hq
           (suc (suc r)) Hr ε ω d
  sqE1 = coh2-frame (suc n) p (suc k) e P₄ (suc q) Hq (suc r) Hr 0 tt
           ε ω θ' d
  dRf' = restr-frame (suc (suc (suc n))) p (suc (suc (suc k))) e P₄
           (suc (suc r)) H₁ ω d
  dEf' = restr-frame (suc (suc (suc n))) p (suc (suc (suc k))) e P₄
           (suc (suc (suc q))) Hq ε d
  bC = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ 0 tt θ' dRf'
  bD = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ 0 tt θ' dEf'
  κ'C = coh-frame (suc (suc n)) p (suc (suc k)) e P₄ (suc r) H₁ 0 tt
          ω θ' d
  c̃C = restr-painting (suc (suc n)) p (suc (suc k)) e P₃ E₄ (suc r) H₁
         ω b' (l θ')
  κ'E = coh-frame (suc (suc n)) p (suc (suc k)) e P₄ (suc (suc q)) Hq
          0 tt ε θ' d
  c̃E = restr-painting (suc (suc n)) p (suc (suc k)) e P₃ E₄
         (suc (suc q)) Hq ε b' (l θ')
  D2C = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq 0 tt ε θ' dRf'
  D1E1 = coh-frame (suc n) p (suc k) e P₃ (suc r)
           (le-trans (suc r) (suc q) (suc k) Hr Hq) 0 tt ω θ' dEf'
  fillPE1 = cohLayer-fillP {P = S'} {S2 = S̃} {S3 = S̃} {rf0 = w⁺}
    {rfF = λ z → restr-frame (suc n) p (suc k) e P₂ (suc q) Hq ε z}
    {rfG = λ z → restr-frame (suc n) p (suc k) e P₂ (suc r)
                   (le-trans (suc r) (suc q) (suc k) Hr Hq) ω z}
    {F = λ z c → restr-painting (suc n) p (suc k) e P₂ E₃ (suc q) Hq
                   ε z c}
    {G = λ z c → restr-painting (suc n) p (suc k) e P₂ E₃ (suc r)
                   (le-trans (suc r) (suc q) (suc k) Hr Hq) ω z c}
    {E1 = E1f'}
    {m1 = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc r) H₁
            ω b'}
    {m2 = bC}
    {C2 = κ'C}
    {n1 = restr-frame (suc (suc n)) p (suc (suc k)) e P₃
            (suc (suc q)) Hq ε b'}
    {n2 = bD}
    {D2 = κ'E}
    {C1 = D2C}
    {D1 = D1E1}
    {K = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc r) Hr ε ω b'}
    {aL = c̃C}
    {aR = c̃E}
    (coh-painting (suc n) p (suc k) e P₃ E₄ (suc q) Hq (suc r) Hr ε ω
       b' (l θ'))
    sqE1
  -- shared (suc n)-level maps and values
  r̂fr = λ z → restr-frame (suc n) p (suc k) e P₂ r H₁ ω z
  r̂fs = λ z → restr-frame (suc n) p (suc k) e P₂ s
                (le-trans s r (suc k) Hs H₁) θ z
  r̂fsq = λ z → restr-frame (suc n) p (suc k) e P₂ (suc q) Hq ε z
  r̂fsr = λ z → restr-frame (suc n) p (suc k) e P₂ (suc r)
                 (le-trans (suc r) (suc q) (suc k) Hr Hq) ω z
  r̂ss = λ z → restr-frame (suc n) p (suc k) e P₂ (suc s) HsB θ z
  F̂r = λ z c → restr-painting (suc n) p (suc k) e P₂ E₃ r H₁ ω z c
  Ĝs = λ z c → restr-painting (suc n) p (suc k) e P₂ E₃ s
                 (le-trans s r (suc k) Hs H₁) θ z c
  F̂sq = λ z c → restr-painting (suc n) p (suc k) e P₂ E₃ (suc q) Hq
                  ε z c
  F̂sr = λ z c → restr-painting (suc n) p (suc k) e P₂ E₃ (suc r)
                  (le-trans (suc r) (suc q) (suc k) Hr Hq) ω z c
  lRC = subst S̃ κ'C c̃C
  lED = subst S̃ κ'E c̃E
  -- the C face
  sC = coh-frame (suc n) p (suc k) e P₃ s (le-trans s r (suc k) Hs H₁)
         0 tt θ θ' dRf'
  C2f' = coh-frame (suc (suc n)) p (suc (suc k)) e P₄ (suc r) H₁
           (suc s) Hs ω θ d
  sqC2' = coh2-frame (suc n) p (suc k) e P₄ r H₁ s Hs 0 tt ω θ θ' d
  XC = Ĝs bC lRC
  aRC = F̂sq bC lRC
  fillPC2s' = cohLayer-fillP {P = S'} {S2 = S̃} {S3 = S̃} {rf0 = w⁺}
    {rfF = r̂fr} {rfG = r̂fs} {F = F̂r} {G = Ĝs}
    {E1 = C2f'}
    {m1 = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ s HsS θ b'}
    {m2 = bK}
    {C2 = κ'}
    {n1 = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc r) H₁
            ω b'}
    {n2 = bC}
    {D2 = κ'C}
    {C1 = C2K}
    {D1 = sC}
    {K = coh-frame (suc n) p (suc k) e P₃ r H₁ s Hs ω θ b'}
    {aL = cS̃}
    {aR = c̃C}
    (coh-painting (suc n) p (suc k) e P₃ E₄ r H₁ s Hs ω θ b' (l θ'))
    sqC2'
  dRC = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc s)
          (le-trans s q (suc k) HsHr (le-up q k Hq)) θ dRf'
  dEC = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc (suc q)) Hq
          ε dRf'
  sqC = coh2-frame n p k e P₃ q Hq s HsHr 0 tt ε θ θ' dRf'
  fillC = cohLayer-fillP {P = P'} {S2 = S'} {S3 = S'} {rf0 = w}
    {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs}
    {E1 = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc s) HsHr ε θ
            dRf'}
    {m1 = restr-frame (suc n) p (suc k) e P₂ s
            (le-trans s q (suc k) HsHr (le-up q k Hq)) θ bC}
    {m2 = restr-frame (suc n) p (suc k) e P₂ 0 tt θ' dRC}
    {C2 = sC}
    {n1 = restr-frame (suc n) p (suc k) e P₂ (suc q) Hq ε bC}
    {n2 = restr-frame (suc n) p (suc k) e P₂ 0 tt θ' dEC}
    {D2 = D2C}
    {C1 = coh-frame n p k e P₂ q Hq 0 tt ε θ' dRC}
    {D1 = coh-frame n p k e P₂ s HsB 0 tt θ θ' dEC}
    {K = coh-frame n p k e P₂ q Hq s HsHr ε θ bC}
    {aL = XC}
    {aR = aRC}
    (coh-painting n p k e P₂ E₃ q Hq s HsHr ε θ bC lRC)
    sqC
  -- junction cells of the C face
  -- the D face
  sD = coh-frame (suc n) p (suc k) e P₃ s (le-trans s r (suc k) Hs H₁)
         0 tt θ θ' dEf'
  Hs↑ = le-up s q HsHr
  D2f' = coh-frame (suc (suc n)) p (suc (suc k)) e P₄ (suc (suc q)) Hq
           (suc s) Hs↑ ε θ d
  sqD2' = coh2-frame (suc n) p (suc k) e P₄ (suc q) Hq s Hs↑ 0 tt
            ε θ θ' d
  XD = Ĝs bD lED
  aRD = F̂sr bD lED
  fillPD2s' = cohLayer-fillP {P = S'} {S2 = S̃} {S3 = S̃} {rf0 = w⁺}
    {rfF = r̂fsq} {rfG = r̂fs} {F = F̂sq} {G = Ĝs}
    {E1 = D2f'}
    {m1 = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ s HsS θ b'}
    {m2 = bK}
    {C2 = κ'}
    {n1 = restr-frame (suc (suc n)) p (suc (suc k)) e P₃
            (suc (suc q)) Hq ε b'}
    {n2 = bD}
    {D2 = κ'E}
    {C1 = D2K}
    {D1 = sD}
    {K = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq s Hs↑ ε θ b'}
    {aL = cS̃}
    {aR = c̃E}
    (coh-painting (suc n) p (suc k) e P₃ E₄ (suc q) Hq s Hs↑ ε θ b'
       (l θ'))
    sqD2'
  dRD = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc s)
          (le-trans s r (suc k) Hs H₁) θ dEf'
  dED = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc (suc r)) H₂
          ω dEf'
  sqD = coh2-frame n p k e P₃ r H₂ s Hs 0 tt ω θ θ' dEf'
  fillD = cohLayer-fillP {P = P'} {S2 = S'} {S3 = S'} {rf0 = w}
    {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs}
    {E1 = coh-frame (suc n) p (suc k) e P₃ (suc r)
            (le-trans (suc r) (suc q) (suc k) Hr Hq) (suc s) Hs ω θ
            dEf'}
    {m1 = restr-frame (suc n) p (suc k) e P₂ s
            (le-trans s r (suc k) Hs H₁) θ bD}
    {m2 = restr-frame (suc n) p (suc k) e P₂ 0 tt θ' dRD}
    {C2 = sD}
    {n1 = restr-frame (suc n) p (suc k) e P₂ (suc r)
            (le-trans (suc r) (suc q) (suc k) Hr Hq) ω bD}
    {n2 = restr-frame (suc n) p (suc k) e P₂ 0 tt θ' dED}
    {D2 = D1E1}
    {C1 = coh-frame n p k e P₂ r H₂ 0 tt ω θ' dRD}
    {D1 = coh-frame n p k e P₂ s HsB 0 tt θ θ' dED}
    {K = coh-frame n p k e P₂ r H₂ s Hs ω θ bD}
    {aL = XD}
    {aR = aRD}
    (coh-painting n p k e P₂ E₃ r H₂ s Hs ω θ bD lED)
    sqD
  -- junction cells of the D face
  -- the goal's composite-face factors, their pointwise composites
  -- (the cube's j-faces), and the ∙Πapp correction cells
  dRl' = restr-layer (suc (suc (suc n))) p (suc (suc k)) e P₄ (suc r)
           H₁ ω d l
  dEl' = restr-layer (suc (suc (suc n))) p (suc (suc k)) e P₄
           (suc (suc q)) Hq ε d l
  pC = cong r̂fsq C2f'
  qC = coh-frame (suc n) p (suc k) e P₃ (suc q) Hq (suc s) HsHr ε θ
         dRf'
  βC = coh-layer (suc n) p k e P₃ q Hq s HsHr ε θ dRf' dRl'
  pD = cong r̂fsr D2f'
  qD = coh-frame (suc n) p (suc k) e P₃ (suc r)
         (le-trans (suc r) (suc q) (suc k) Hr Hq) (suc s) Hs ω θ dEf'
  βD = coh-layer (suc n) p k e P₃ r H₂ s Hs ω θ dEf' dEl'
  Rθ = λ y t → restr-frame n p k e P₁ 0 tt t y
  module ΠC = ∙Πapp {P = P'} Rθ pC qC
    (λ ii → restr-layer (suc n) p k e P₂ q Hq ε (C2f' ii)
              (coh-layer (suc (suc n)) p (suc k) e P₄ r H₁ s Hs ω θ
                 d l ii))
    βC θ'
  module ΠD = ∙Πapp {P = P'} Rθ pD qD
    (λ ii → restr-layer (suc n) p k e P₂ r H₂ ω (D2f' ii)
              (coh-layer (suc (suc n)) p (suc k) e P₄ (suc q) Hq s
                 Hs↑ ε θ d l ii))
    βD θ'

-- The painting 2-coherence.  The s = 0 case is the filler of the layer
-- coherence's square composition; the s, r, q ≥ 1 case at suc k pairs
-- the layer 2-coherence with the recursive painting 2-coherence.
coh2-painting n p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) E q Hq r Hr zero Hs ε ω θ
              d (l , c) =
  cohLayer-fillP
    {P = λ x → GDom (painting n p k e D E₁ x)}
    {S2 = λ m → GDom (painting (suc n) p (suc k) e P₁ E₂ m)}
    {S3 = λ m → GDom (painting (suc n) p (suc k) e P₁ E₂ m)}
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
    (coh2-frame n p k e P₃ q Hq r Hr 0 tt ε ω θ d)
  where
  P₁ = (D ∷ E₁)
  P₂ = ((D ∷ E₁) ∷ E₂)
  P₃ = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  dR = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc r) H₁ ω d
  dE = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ (suc (suc q)) Hq ε d
  b : (θ : arity) → GDom (frame (suc (suc n)) p (suc (suc k)) e P₂)
  b θ = restr-frame (suc (suc n)) p (suc (suc k)) e P₃ 0 tt θ d
coh2-painting n p k e D E q Hq zero    Hr (suc s) ()
coh2-painting n p k e D E zero    Hq (suc r) ()
coh2-painting n p zero    e D E (suc q) ()
coh2-painting n p (suc k) e (((D ∷ E₁) ∷ E₂) ∷ E₃) E (suc q) Hq (suc r)
              Hr (suc s) Hs ε ω θ d (l , c) i j =
  Σ≡hex.Dep.hexᵈ
    {A = GDom (frame n p (suc k) e D)}
    {B = λ d' → GDom (layer n p k e D d')}
    (λ i' → restr-frame n p (suc k) e (D ∷ E₁) (suc q) Hq ε (C2f i'))
    (coh-frame n p (suc k) e ((D ∷ E₁) ∷ E₂) (suc q) Hq (suc s) HsHr
       ε θ dRf)
    (λ i' → restr-layer n p k e (D ∷ E₁) q Hq ε (C2f i') (C2s i'))
    (coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq s HsHr ε θ dRf dRl)
    (λ i' → restr-frame n p (suc k) e (D ∷ E₁) (suc r) H₂ ω (D2f i'))
    (coh-frame n p (suc k) e ((D ∷ E₁) ∷ E₂) (suc r) H₂ (suc s) Hs
       ω θ dEf)
    (λ i' → restr-layer n p k e (D ∷ E₁) r H₂ ω (D2f i') (D2s i'))
    (coh-layer n p k e ((D ∷ E₁) ∷ E₂) r H₂ s Hs ω θ dEf dEl)
    (coh-frame n p (suc k) e ((D ∷ E₁) ∷ E₂) (suc q) Hq (suc r) Hr ε ω
       dSf)
    (coh-layer n p k e ((D ∷ E₁) ∷ E₂) q Hq r Hr ε ω dSf dSl)
    (λ i' → restr-frame n p (suc k) e (D ∷ E₁) (suc s) HsB θ (E1f i'))
    (λ i' → restr-layer n p k e (D ∷ E₁) s HsB θ (E1f i') (E1s i'))
    (coh2-frame n p (suc k) e (((D ∷ E₁) ∷ E₂) ∷ E₃) (suc q) Hq (suc r)
       Hr (suc s) Hs ε ω θ d)
    (coh2-layer n p k e (((D ∷ E₁) ∷ E₂) ∷ E₃) q Hq r Hr s Hs ε ω θ
       d l)
    {M = λ x → GDom (painting n (suc p) k e D E₁ x)}
    (λ i' → restr-painting n (suc p) k e (D ∷ E₁) E₂ q Hq ε
              (C2f i' , C2s i') (C2c i'))
    (coh-painting n (suc p) k e ((D ∷ E₁) ∷ E₂) E₃ q Hq s HsHr ε θ
       (dRf , dRl) dRc)
    (λ i' → restr-painting n (suc p) k e (D ∷ E₁) E₂ r H₂ ω
              (D2f i' , D2s i') (D2c i'))
    (coh-painting n (suc p) k e ((D ∷ E₁) ∷ E₂) E₃ r H₂ s Hs ω θ
       (dEf , dEl) dEc)
    (coh-painting n (suc p) k e ((D ∷ E₁) ∷ E₂) E₃ q Hq r Hr ε ω
       (dSf , dSl) dSc)
    (λ i' → restr-painting n (suc p) k e (D ∷ E₁) E₂ s HsB θ
              (E1f i' , E1s i') (E1c i'))
    (coh2-painting n (suc p) k e (((D ∷ E₁) ∷ E₂) ∷ E₃) E q Hq r Hr
       s Hs ε ω θ (d , l) c)
    i j
  where
  PP = (((D ∷ E₁) ∷ E₂) ∷ E₃)
  H₁ = le-trans r q (suc k) Hr (le-up q k Hq)
  H₂ = le-trans r q k Hr Hq
  HsHr = le-trans s r q Hs Hr
  Hs↑ = le-up s q (le-trans s r q Hs Hr)
  HsB = le-trans s r k Hs (le-trans r q k Hr Hq)
  HsS = le-up s (suc k) (le-up s k HsB)
  C2f = coh-frame (suc n) p (suc (suc k)) e PP (suc r) H₁ (suc s) Hs
          ω θ d
  C2s = coh-layer (suc n) p (suc k) e PP r H₁ s Hs ω θ d l
  C2c = coh-painting (suc n) (suc p) (suc k) e PP E r H₁ s Hs ω θ
          (d , l) c
  D2f = coh-frame (suc n) p (suc (suc k)) e PP (suc (suc q)) Hq (suc s)
          Hs↑ ε θ d
  D2s = coh-layer (suc n) p (suc k) e PP (suc q) Hq s Hs↑ ε θ d l
  D2c = coh-painting (suc n) (suc p) (suc k) e PP E (suc q) Hq s Hs↑
          ε θ (d , l) c
  E1f = coh-frame (suc n) p (suc (suc k)) e PP (suc (suc q)) Hq
          (suc (suc r)) Hr ε ω d
  E1s = coh-layer (suc n) p (suc k) e PP (suc q) Hq (suc r) Hr ε ω d l
  E1c = coh-painting (suc n) (suc p) (suc k) e PP E (suc q) Hq (suc r)
          Hr ε ω (d , l) c
  dRf = restr-frame (suc (suc n)) p (suc (suc (suc k))) e PP
          (suc (suc r)) H₁ ω d
  dRl = restr-layer (suc (suc n)) p (suc (suc k)) e PP (suc r) H₁ ω d l
  dRc = restr-painting (suc (suc n)) (suc p) (suc (suc k)) e PP E
          (suc r) H₁ ω (d , l) c
  dEf = restr-frame (suc (suc n)) p (suc (suc (suc k))) e PP
          (suc (suc (suc q))) Hq ε d
  dEl = restr-layer (suc (suc n)) p (suc (suc k)) e PP (suc (suc q)) Hq
          ε d l
  dEc = restr-painting (suc (suc n)) (suc p) (suc (suc k)) e PP E
          (suc (suc q)) Hq ε (d , l) c
  dSf = restr-frame (suc (suc n)) p (suc (suc (suc k))) e PP (suc s)
          HsS θ d
  dSl = restr-layer (suc (suc n)) p (suc (suc k)) e PP s HsS θ d l
  dSc = restr-painting (suc (suc n)) (suc p) (suc (suc k)) e PP E s
          HsS θ (d , l) c

------------------------------------------------------------------------
-- The tower
------------------------------------------------------------------------

-- The full frame at dimension n: the one whose index is the length,
-- at the fuel that IS the length.
fullframe : {n : ℕ} (D : Pre n) → HGpd₀
fullframe {n} D = frame n n 0 (eqN-refl n) D

record νGpd→ (n : ℕ) (D : Pre n) : Set₁ where
  coinductive
  constructor _∷ν_
  field
    this : Fil n 0 D
    next : νGpd→ (suc n) (D ∷ this)
open νGpd→ public

νGpds : Set₁
νGpds = νGpd→ 0 tt*
