------------------------------------------------------------------------
-- examples.Examples — the νSet gate: instantiations and the level-4
-- example.  Fillers are written with the dimension-polymorphic prefix
-- `λ m f d → …`; the compute gate `frame4` normalizes with every
-- dimension argument closed, so all of them reduce away.
------------------------------------------------------------------------

{-# OPTIONS --rewriting #-}

module examples.Examples where

open import Bonak.Prelude
open import Bonak.NatRew
import Bonak.νSet

module Simplicial = Bonak.νSet ⊤
module Cubes = Bonak.νSet Bool

AugmentedSemiSimplicial : Set₁
AugmentedSemiSimplicial = Simplicial.νSets

SemiSimplicial : Set₁
SemiSimplicial = Simplicial.νSet→ 1 (tt* Simplicial.∷ λ m f d → hunit)

SemiCubical : Set₁
SemiCubical = Cubes.νSets

SemiSimplicial4 : Set₁
SemiSimplicial4 = Simplicial.Pre 4

-- The point prefix at dimension 4: building it forces every filler
-- type — hence frame / layer / painting / restr-* / coh-* at
-- dimensions 0..3 — to reduce.
pt4 : SemiSimplicial4
pt4 = ((((tt* Simplicial.∷ (λ m f d → hunit))
         Simplicial.∷ (λ m f d → hunit))
        Simplicial.∷ (λ m f d → hunit))
       Simplicial.∷ (λ m f d → hunit))

-- and its full frame at dimension 4, the type the next filler eats.
frame4 : Set
frame4 = Dom (Simplicial.frame 4 4 0 tt pt4)
