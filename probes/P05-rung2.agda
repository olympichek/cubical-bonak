{-# OPTIONS --cubical --prop --guardedness #-}

-- P05: the rung-2 reproducer for the νGpd part-3 port.  The wall is the
-- ELABORATION OF ONE APPLICATION — mkCohFrames at a concrete top-storey
-- extension.  Measured (Agda 2.8.0, 2026-08-12):
--   * rung2m (abstract extension, below)                       0.3 s
--   * the same telescope with no application at all            0.4 s
--   * rung2k (commented out below): the extension concrete,
--     cps/Q2 ABSTRACT, every spelling syntactically identical
--     to the expected types                                  > 70 s DNF
--   * the same inside the real mkCoh2Frame / mkCoh2FrameType  > 15 min DNF
--     (also DNF under Agda 2.9.0-dev, with and without
--      AGDA_CONVERSION_CACHE=1)
-- So the cost is the type-level unfolding of the tower functions
-- (mkExtraDeps / mkRestrPaintings / mkCohFrameTypes / mkRestrFrames) at
-- a CONSTRUCTOR-headed extension one storey up — not the Square types
-- (mkCoh2FrameType is already opaque) and not any proof term.

module probes.P05-rung2 (arity : Set) where

open import Bonak.Prelude
open import Bonak.LeProp
open import Bonak.RewLemmas
open import Bonak.νGpd arity

-- Control: abstract extension — 0.3 s.
rung2m : {p k : ℕ} {dc : DepsCohs p k}
  (eDC : DepsCohsExtension p k dc)
  (cps : mkCohPaintingTypes eDC)
  (Q2 : mkCoh2FrameTypes eDC cps)
  → mkCohFrameTypes (mkExtraDeps eDC) (mkRestrPaintings eDC)
rung2m eDC cps Q2 = mkCohFrames eDC cps Q2

-- The wall: uncomment to reproduce (does not terminate in 15 min).
--
-- rung2k : {p k : ℕ} {dc2 : DepsCohs2 (suc p) k}
--   (eDC2 : DepsCohs2Extension (suc p) k dc2)
--   (cps : mkCohPaintingTypes (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))
--   (Q2 : mkCoh2FrameTypes (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)) cps)
--   → mkCohFrameTypes
--       (mkExtraDeps (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))
--       (mkRestrPaintings (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)))
-- rung2k {p} {k} {dc2} eDC2 cps Q2 =
--   mkCohFrames (AddCohDep (mkDepsCohs dc2) (mkExtraCohs eDC2)) cps Q2
