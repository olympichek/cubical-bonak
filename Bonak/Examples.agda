------------------------------------------------------------------------
-- Bonak.Examples — the νSet.v instantiations: simplicial (arity ⊤) and
-- cubical (arity Bool), and the SemiSimplicial4 gate.
------------------------------------------------------------------------

module Bonak.Examples where

open import Bonak.Prelude
import Bonak.νSet

module Simplicial = Bonak.νSet ⊤
module Cubes = Bonak.νSet Bool

AugmentedSemiSimplicial : Set₁
AugmentedSemiSimplicial = Simplicial.νSets

SemiSimplicial : Set₁
SemiSimplicial = Simplicial.νSetFrom 1 (tt* , λ _ → hunit)

SemiCubical : Set₁
SemiCubical = Cubes.νSets

-- The Rocq gate: Eval compute in (νSetAt 4).(prefix).
SemiSimplicial4 : Set₁
SemiSimplicial4 = Simplicial.prefix (Simplicial.νSetAt 4)
