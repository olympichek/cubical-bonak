------------------------------------------------------------------------
-- probes.Examples — the νSet gate: instantiations and the level-4 example.
------------------------------------------------------------------------

{-# OPTIONS --rewriting #-}

module probes.Examples where

open import Bonak.Prelude
open import Bonak.NatRew
import Bonak.νSet

module Simplicial = Bonak.νSet ⊤
module Cubes = Bonak.νSet Bool

AugmentedSemiSimplicial : Set₁
AugmentedSemiSimplicial = Simplicial.νSets

SemiSimplicial : Set₁
SemiSimplicial = Simplicial.νSet→ 1 (tt* Simplicial.∷ λ _ → hunit)

SemiCubical : Set₁
SemiCubical = Cubes.νSets

-- The V1 gate, transposed: V1's `prefix (νSetAt 4)` is by construction
-- the list of 4 fillers, which fillers-only storage calls `Pre 4`.
SemiSimplicial4 : Set₁
SemiSimplicial4 = Simplicial.Pre 4

-- A compute gate with an inhabitant: building the point prefix at
-- dimension 4 forces every filler type — hence frame / layer / painting
-- / restr-* / coh-* at dimensions 0..3 — to reduce.
pt4 : SemiSimplicial4
pt4 = ((((tt* Simplicial.∷ (λ _ → hunit)) Simplicial.∷ (λ _ → hunit))
        Simplicial.∷ (λ _ → hunit)) Simplicial.∷ (λ _ → hunit))

-- and its full frame at dimension 4, the type the next filler eats.
-- Normalizing this is the compute gate (see V4-REPORT.md): it runs
-- frame / layer / painting / restr-* / coh-* at dimensions 0..4.
frame4 : Set
frame4 = Dom (Simplicial.frame 4 0 pt4)
