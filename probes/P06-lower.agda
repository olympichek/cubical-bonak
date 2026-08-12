{-# OPTIONS --cubical --prop --guardedness #-}
-- P06: is the P05 wall specific to the coh storey, or does the same
-- application one storey lower (mkRestrFrames at a concrete extension)
-- already cost?
module probes.P06-lower (arity : Set) where
open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas
open import Bonak.νGpd arity

lower : {p k : ℕ} {dc : DepsCohs (suc p) k}
  (eDC : DepsCohsExtension (suc p) k dc)
  (rps : mkRestrPaintingTypes (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC)))
  (Q : mkCohFrameTypes (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC)) rps)
  → _
lower {p} {k} {dc} eDC rps Q =
  mkRestrFrames (AddRestrDep (mkDepsRestr dc) (mkExtraDeps eDC)) rps Q
