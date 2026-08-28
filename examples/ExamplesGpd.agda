------------------------------------------------------------------------
-- examples.ExamplesGpd — the νGpd gate: instantiations and the level-5
-- example.  Fillers are written with the dimension-polymorphic prefix
-- `λ m f d → …`; the compute gate `frame5` normalizes with every
-- dimension argument closed, so all of them — and the frame / layer /
-- painting / restr-* / coh-* / coh2-* bodies at dimensions 0..4 they
-- force — reduce away:
-- its normal form is a closed Σ/Π/⊤ nest with zero transp/hcomp.
------------------------------------------------------------------------

{-# OPTIONS --rewriting #-}

module examples.ExamplesGpd where

open import Bonak.Prelude
open import Bonak.NatRew
import Bonak.νGpd

module Simplicial = Bonak.νGpd ⊤
module Cubes = Bonak.νGpd Bool

AugmentedSemiSimplicialGpd : Set₁
AugmentedSemiSimplicialGpd = Simplicial.νGpds

SemiSimplicialGpd : Set₁
SemiSimplicialGpd = Simplicial.νGpd→ 1 (tt* Simplicial.∷ λ m f d → gunit)

SemiCubicalGpd : Set₁
SemiCubicalGpd = Cubes.νGpds

SemiSimplicial5 : Set₁
SemiSimplicial5 = Simplicial.Pre 5

-- The point prefix at dimension 5: building it forces every filler
-- type — hence the tower's members at dimensions 0..4 — to reduce.
pt5 : SemiSimplicial5
pt5 = (((((tt* Simplicial.∷ (λ m f d → gunit))
          Simplicial.∷ (λ m f d → gunit))
         Simplicial.∷ (λ m f d → gunit))
        Simplicial.∷ (λ m f d → gunit))
       Simplicial.∷ (λ m f d → gunit))

-- and its full frame at dimension 5, the type the next filler eats.
frame5 : Set
frame5 = GDom (Simplicial.frame 5 5 0 tt pt5)
