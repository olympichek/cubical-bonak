------------------------------------------------------------------------
-- Bonak.LayerHexBridge — the Π-layer analogue of νGpd/Layer.v's
-- Hexagon section (lmap2_hex_rew_eq / layer_dpath2_eq / nth_dpath_*).
--
-- With layers as literal Π-types, a PathP between layers is a function
-- of PathPs *definitionally* (λ-exchange), so the Rocq layer-2-cell
-- extensionality (layer_dpath2_eq) shrinks to: conjugate the two
-- subst-form 2-cells through toPathP/fromPathP, exchange the ω-binder
-- with the two path binders, and convert back (Π-hex-bridge below).
--
-- The rest of the file is the Πcomp-commutation suite (Rocq's
-- nth_dpath_trans / nth_dpath_sigT_map_eq / nth_dpath_lmap2_rew_eq):
-- the ω-component of each composite 2-cell factor is computed for
-- ⊙ (Πcomp-⊙), sigT-map-eq of a pointwise layer map
-- (Πcomp-sigT-map-eq), RewLemmas' Π-subst-ext (Πcomp-Π-subst-ext, via
-- the JRefl-identification with the cubical assembly Π-ext'), plain
-- right composition (Πcomp-∙), transport along an index 2-cell
-- (Πcomp-subst2), cong-of-subst (Πcomp-cong-subst), and refl-index
-- paths (Πcomp-refl), with the Π-transport noise isolated in noiseΠ.
-- With these, mkCoh2Layer's proof reduces to GpdLemmas'
-- rew-coh2Layer + one GUIP cell; see νGpd.agda's resume block.
------------------------------------------------------------------------

module Bonak.LayerHexBridge where

open import Bonak.Prelude
open import Bonak.RewLemmas
open import Bonak.GpdLemmas

private variable
  ℓ ℓ' ℓ'' ℓ''' : Level

-- The ω-component of a Π-subst-equation (Rocq's nth_dpath).

Πcomp : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
        {t1 t2 : T} {e : t1 ≡ t2}
        {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
        (u : subst (λ t → (ω : A') → B ω t) e f ≡ g) (ω : A')
        → subst (B ω) e (f ω) ≡ g ω
Πcomp {A' = A'} {B = B} {e = e} {f = f} {g = g} u ω =
  fromPathP {P = λ i → B ω (e i)} {x = f ω} {y = g ω}
    (λ i → toPathP {P = λ i → (ω' : A') → B ω' (e i)} {x = f} {y = g} u i ω)

-- Inverse of GpdLemmas.toPathP-over: recover the subst-form 2-cell
-- from a PathP square between the toPathP-images.

fromPathP-over : {A : Set ℓ} {Q : A → Set ℓ'} {x y : A}
  {p1 p2 : x ≡ y} (κ : p1 ≡ p2) {a : Q x} {b : Q y}
  (u : subst Q p1 a ≡ b) (v : subst Q p2 a ≡ b)
  (SQ : PathP (λ k → PathP (λ i → Q (κ k i)) a b)
              (toPathP {P = λ i → Q (p1 i)} u)
              (toPathP {P = λ i → Q (p2 i)} v))
  → subst (λ p → subst Q p a ≡ b) κ u ≡ v
fromPathP-over {Q = Q} {p1 = p1} κ {a} {b} u =
  J (λ p2 κ → (v : subst Q p2 a ≡ b)
              → PathP (λ k → PathP (λ i → Q (κ k i)) a b)
                      (toPathP {P = λ i → Q (p1 i)} u)
                      (toPathP {P = λ i → Q (κ i1 i)} v)
              → subst (λ p → subst Q p a ≡ b) κ u ≡ v)
    (λ v SQ → substRefl (λ p → subst Q p a ≡ b) u
              ∙ sym (fromPathP-toPathP (λ i → Q (p1 i)) u)
              ∙ cong (fromPathP {P = λ i → Q (p1 i)}) SQ
              ∙ fromPathP-toPathP (λ i → Q (p1 i)) v)
    κ

-- The hexagon transfer: a 2-cell between transported Π-valued
-- subst-equations follows from its ω-components (Rocq's
-- layer_dpath2_eq, with ext2 replaced by the definitional λ-exchange).

Π-hex-bridge :
  {A' : Set ℓ} {X : Set ℓ'} {B : A' → X → Set ℓ''}
  {x y : X} {e1 e2 : x ≡ y} (κ : e1 ≡ e2)
  {f : (ω : A') → B ω x} {g : (ω : A') → B ω y}
  (u : subst (λ x' → (ω : A') → B ω x') e1 f ≡ g)
  (v : subst (λ x' → (ω : A') → B ω x') e2 f ≡ g)
  (H : (ω : A') → subst (λ e → subst (B ω) e (f ω) ≡ g ω) κ
                    (Πcomp {B = B} {e = e1} {f = f} {g = g} u ω)
                  ≡ Πcomp {B = B} {e = e2} {f = f} {g = g} v ω)
  → subst (λ e → subst (λ x' → (ω : A') → B ω x') e f ≡ g) κ u ≡ v
Π-hex-bridge {A' = A'} {B = B} {x = x} {y = y} {e1 = e1} {e2 = e2} κ
             {f = f} {g = g} u v H =
  fromPathP-over {Q = λ x' → (ω : A') → B ω x'} κ u v
    (λ k i ω → sq' ω k i)
  where
  -- the toPathP-lines of u and v, and their ω-components
  ru : PathP (λ i → (ω : A') → B ω (e1 i)) f g
  ru = toPathP {P = λ i → (ω : A') → B ω (e1 i)} u
  rv : PathP (λ i → (ω : A') → B ω (e2 i)) f g
  rv = toPathP {P = λ i → (ω : A') → B ω (e2 i)} v

  cu : (ω : A') → subst (B ω) e1 (f ω) ≡ g ω
  cu ω = Πcomp {B = B} {e = e1} {f = f} {g = g} u ω
  cv : (ω : A') → subst (B ω) e2 (f ω) ≡ g ω
  cv ω = Πcomp {B = B} {e = e2} {f = f} {g = g} v ω

  -- the square over κ from the pointwise hypothesis
  sq : (ω : A') → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                        (toPathP {P = λ i → B ω (e1 i)} (cu ω))
                        (toPathP {P = λ i → B ω (e2 i)} (cv ω))
  sq ω = subst (λ z → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                            (toPathP {P = λ i → B ω (e1 i)} (cu ω)) z)
               (cong (toPathP {P = λ i → B ω (e2 i)}) (H ω))
               (toPathP-over {Q = B ω} κ (cu ω))

  -- endpoint corrections: toPathP (Πcomp u ω) is toPathP∘fromPathP of
  -- the ω-component line of u
  sq' : (ω : A') → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                         (λ i → ru i ω) (λ i → rv i ω)
  sq' ω =
    subst (λ z → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                       z (λ i → rv i ω))
          (toPathP-fromPathP (λ i → B ω (e1 i)) {x = f ω} {y = g ω}
            (λ i → ru i ω))
      (subst (λ z → PathP (λ k → PathP (λ i → B ω (κ k i)) (f ω) (g ω))
                          (toPathP {P = λ i → B ω (e1 i)} (cu ω)) z)
             (toPathP-fromPathP (λ i → B ω (e2 i)) {x = f ω} {y = g ω}
               (λ i → rv i ω))
             (sq ω))

------------------------------------------------------------------------
-- The Πcomp-commutation suite (Rocq's nth_dpath_* lemmas).
------------------------------------------------------------------------

-- The cubical assembly of a layer path from its components (the clean
-- counterpart of RewLemmas.Π-subst-ext; they agree, see below).

Π-ext' : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
         {t1 t2 : T} (e : t1 ≡ t2)
         {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
         (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω)
         → subst (λ t → (ω : A') → B ω t) e f ≡ g
Π-ext' {A' = A'} {B = B} e {f} {g} H =
  fromPathP {P = λ i → (ω : A') → B ω (e i)} {x = f} {y = g}
    (λ i ω → toPathP {P = λ i → B ω (e i)} {x = f ω} {y = g ω} (H ω) i)

-- Πcomp is a retraction of Π-ext' (both round trips are the
-- toPathP/fromPathP ones).

Πcomp-Π-ext' : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2)
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω) (ω : A')
  → Πcomp {B = B} {e = e} {f = f} {g = g} (Π-ext' {B = B} e {f = f} {g = g} H) ω ≡ H ω
Πcomp-Π-ext' {A' = A'} {B = B} e {f} {g} H ω =
  cong (λ (w : PathP (λ i → (ω' : A') → B ω' (e i)) f g)
          → fromPathP {P = λ i → B ω (e i)} {x = f ω} {y = g ω}
              (λ i → w i ω))
       (toPathP-fromPathP (λ i → (ω' : A') → B ω' (e i)) {x = f} {y = g}
         (λ i ω' → toPathP {P = λ i → B ω' (e i)} {x = f ω'} {y = g ω'}
                     (H ω') i))
  ∙ fromPathP-toPathP (λ i → B ω (e i)) {x = f ω} {y = g ω} (H ω)

-- RewLemmas' J-built Π-subst-ext agrees with Π-ext' (JRefl plus the
-- constant-line values of toPathP/fromPathP).

Π-subst-ext≡Π-ext' : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2)
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω)
  → Π-subst-ext {B = B} e {f = f} {g = g} H ≡ Π-ext' {B = B} e {f = f} {g = g} H
Π-subst-ext≡Π-ext' {A' = A'} {T = T} {B = B} {t1 = t1} e {f} {g} H =
  J (λ t2 e → {g : (ω : A') → B ω t2}
              (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω)
              → Π-subst-ext {B = B} e {f = f} {g = g} H
                ≡ Π-ext' {B = B} e {f = f} {g = g} H)
    (λ {g} H →
      cong (λ (F : {g : (ω : A') → B ω t1}
                   → ((ω : A') → subst (B ω) refl (f ω) ≡ g ω)
                   → subst (λ d → (ω : A') → B ω d) refl f ≡ g)
              → F {g = g} H)
           (JRefl (λ _ E1 → {g : _}
                            → ((ω : _) → subst (B ω) E1 (f ω) ≡ g ω)
                            → subst (λ d → (ω : _) → B ω d) E1 f ≡ g)
                  (λ {g} H → transportRefl f
                             ∙ funExt (λ ω → sym (transportRefl (f ω))
                                             ∙ H ω)))
      ∙ sym (cong (λ (h : (ω : A') → f ω ≡ g ω)
                     → transportRefl f ∙ funExt h)
                  (funExt (λ ω → toPathPConst {x = f ω} {y = g ω} (H ω))))
      ∙ sym (fromPathPConst {x = f} {y = g}
              (λ i ω → toPathP {P = λ _ → B ω t1}
                         {x = f ω} {y = g ω} (H ω) i)))
    e H

Πcomp-Π-subst-ext : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2)
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (H : (ω : A') → subst (B ω) e (f ω) ≡ g ω) (ω : A')
  → Πcomp {B = B} {e = e} {f = f} {g = g}
      (Π-subst-ext {B = B} e {f = f} {g = g} H) ω ≡ H ω
Πcomp-Π-subst-ext {B = B} {t1 = t1} {t2 = t2} e {f} {g} H ω =
  cong (λ u → Πcomp {B = B} {e = e} {f = f} {g = g} u ω)
       (Π-subst-ext≡Π-ext' {B = B} e {f = f} {g = g} H)
  ∙ Πcomp-Π-ext' {B = B} e {f = f} {g = g} H ω

-- Πcomp commutes with transporting along a 2-cell of index paths
-- (needed to push components through ⊙'s defining subst).

Πcomp-subst2 : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} {e e' : t1 ≡ t2} (S : e ≡ e')
  {f : (ω : A') → B ω t1} {g : (ω : A') → B ω t2}
  (M : subst (λ t → (ω' : A') → B ω' t) e f ≡ g) (ω : A')
  → Πcomp {B = B} {e = e'} {f = f} {g = g}
      (subst (λ e0 → subst (λ t → (ω' : A') → B ω' t) e0 f ≡ g) S M) ω
    ≡ subst (λ e0 → subst (B ω) e0 (f ω) ≡ g ω) S
        (Πcomp {B = B} {e = e} {f = f} {g = g} M ω)
Πcomp-subst2 {A' = A'} {B = B} {e = e} S {f = f} {g = g} M ω =
  J (λ e' S → Πcomp {B = B} {e = e'} {f = f} {g = g}
                (subst (λ e0 → subst (λ t → (ω' : A') → B ω' t) e0 f ≡ g)
                       S M) ω
              ≡ subst (λ e0 → subst (B ω) e0 (f ω) ≡ g ω) S
                  (Πcomp {B = B} {e = e} {f = f} {g = g} M ω))
    (cong (λ M' → Πcomp {B = B} {e = e} {f = f} {g = g} M' ω)
          (substRefl (λ e0 → subst (λ t → (ω' : A') → B ω' t) e0 f ≡ g) M)
     ∙ sym (substRefl (λ e0 → subst (B ω) e0 (f ω) ≡ g ω)
             (Πcomp {B = B} {e = e} {f = f} {g = g} M ω)))
    S

-- Πcomp past a fiberwise layer map (Rocq's nth_dpath_sigT_map_eq):
-- the Σ-map is pointwise, so both sides shrink to the same center by
-- one toPathP∘fromPathP round trip each.

Πcomp-sigT-map-eq :
  {ℓs ℓp : Level}
  {A' : Set ℓ} {T : Set ℓ'} {T' : Set ℓ''}
  {S : A' → T → Set ℓs} {P : A' → T' → Set ℓp}
  {fA : T → T'} (NA : (t : T) (ω : A') → S ω t → P ω (fA t))
  {d1 d2 : T} {p : d1 ≡ d2}
  {u : (ω : A') → S ω d1} {v : (ω : A') → S ω d2}
  (M : subst (λ t → (ω : A') → S ω t) p u ≡ v) (ω : A')
  → Πcomp {B = P} {e = cong fA p}
      {f = λ ω' → NA d1 ω' (u ω')} {g = λ ω' → NA d2 ω' (v ω')}
      (sigT-map-eq {P = λ t → (ω' : A') → S ω' t}
                   {Q = λ t' → (ω' : A') → P ω' t'} {f = fA}
                   (λ t ll ω' → NA t ω' (ll ω'))
                   {x = d1} {y = d2} {u = u} {v = v} {p = p} M) ω
    ≡ sigT-map-eq {P = S ω} {Q = P ω} {f = fA} (λ t x → NA t ω x)
        {x = d1} {y = d2} {u = u ω} {v = v ω} {p = p}
        (Πcomp {B = S} {e = p} {f = u} {g = v} M ω)
Πcomp-sigT-map-eq {A' = A'} {S = S} {P = P} {fA = fA} NA
                  {d1} {d2} {p} {u} {v} M ω =
  cong (λ (w : PathP (λ i → (ω' : A') → P ω' (fA (p i)))
                     (λ ω' → NA d1 ω' (u ω')) (λ ω' → NA d2 ω' (v ω')))
          → fromPathP {P = λ i → P ω (fA (p i))}
              {x = NA d1 ω (u ω)} {y = NA d2 ω (v ω)} (λ i → w i ω))
       (toPathP-fromPathP (λ i → (ω' : A') → P ω' (fA (p i)))
         {x = λ ω' → NA d1 ω' (u ω')} {y = λ ω' → NA d2 ω' (v ω')}
         (λ i ω' → NA (p i) ω'
            (toPathP {P = λ i → (ω'' : A') → S ω'' (p i)} {x = u} {y = v}
              M i ω')))
  ∙ sym (cong (λ (w : PathP (λ i → S ω (p i)) (u ω) (v ω))
                 → fromPathP {P = λ i → P ω (fA (p i))}
                     {x = NA d1 ω (u ω)} {y = NA d2 ω (v ω)}
                     (λ i → NA (p i) ω (w i)))
              (toPathP-fromPathP (λ i → S ω (p i)) {x = u ω} {y = v ω}
                (λ i → toPathP {P = λ i → (ω'' : A') → S ω'' (p i)}
                         {x = u} {y = v} M i ω)))

-- Πcomp past a right homogeneous composition factor.

Πcomp-∙ : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} {e : t1 ≡ t2}
  {f : (ω : A') → B ω t1} {g h : (ω : A') → B ω t2}
  (α : subst (λ t → (ω : A') → B ω t) e f ≡ g) (β : g ≡ h) (ω : A')
  → Πcomp {B = B} {e = e} {f = f} {g = h} (α ∙ β) ω
    ≡ Πcomp {B = B} {e = e} {f = f} {g = g} α ω ∙ funExt⁻ β ω
Πcomp-∙ {A' = A'} {B = B} {e = e} {f = f} {g = g} α β ω =
  J (λ h β → Πcomp {B = B} {e = e} {f = f} {g = h} (α ∙ β) ω
             ≡ Πcomp {B = B} {e = e} {f = f} {g = g} α ω ∙ funExt⁻ β ω)
    (cong (λ z → Πcomp {B = B} {e = e} {f = f} {g = g} z ω)
          (sym (rUnit α))
     ∙ rUnit (Πcomp {B = B} {e = e} {f = f} {g = g} α ω))
    β

-- The Π-transport noise path: applying a transported layer at ω versus
-- transporting the component.

noiseΠ : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} (e : t1 ≡ t2) (u : (ω : A') → B ω t1) (ω : A')
  → subst (λ t → (ω' : A') → B ω' t) e u ω ≡ subst (B ω) e (u ω)
noiseΠ {A' = A'} {B = B} e u ω =
  J (λ t2 e → subst (λ t → (ω' : A') → B ω' t) e u ω
              ≡ subst (B ω) e (u ω))
    (funExt⁻ (transportRefl u) ω ∙ sym (transportRefl (u ω)))
    e

-- noiseΠ computed at refl (JRefl unfolding).

noiseΠ-refl : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 : T} (u : (ω : A') → B ω t1) (ω : A')
  → noiseΠ {B = B} (refl {x = t1}) u ω
    ≡ funExt⁻ (transportRefl u) ω ∙ sym (transportRefl (u ω))
noiseΠ-refl {A' = A'} {T = T} {B = B} {t1 = t1} u ω =
  JRefl (λ t2 e → subst (λ t → (ω' : A') → B ω' t) e u ω
                  ≡ subst (B ω) e (u ω))
        (funExt⁻ (transportRefl u) ω ∙ sym (transportRefl (u ω)))

-- The ω-component of a layer path over a refl index: funExt⁻ up to the
-- noise conjugator.

Πcomp-refl : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 : T} {f g : (ω : A') → B ω t1}
  (X : subst (λ t → (ω : A') → B ω t) (refl {x = t1}) f ≡ g) (ω : A')
  → Πcomp {B = B} {e = refl} {f = f} {g = g} X ω
    ≡ sym (noiseΠ {B = B} refl f ω) ∙ funExt⁻ X ω
Πcomp-refl {A' = A'} {B = B} {t1 = t1} {f = f} {g = g} X ω =
  fromPathPConst {x = f ω} {y = g ω}
    (λ i → toPathP {P = λ _ → (ω' : A') → B ω' t1} {x = f} {y = g} X i ω)
  ∙ cong (λ (w : f ≡ g) → transportRefl (f ω) ∙ funExt⁻ w ω)
         (toPathPConst {x = f} {y = g} X)
  ∙ sym (∙-assoc (transportRefl (f ω))
                 (sym (funExt⁻ (transportRefl f) ω)) (funExt⁻ X ω))
  ∙ cong (_∙ funExt⁻ X ω)
      (sym (cong sym (noiseΠ-refl {B = B} f ω)
            ∙ symDistr (funExt⁻ (transportRefl f) ω)
                       (sym (transportRefl (f ω)))))

-- The ω-component of a cong-of-subst along an index 2-cell.

Πcomp-cong-subst : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 t2 : T} {e1 e2 : t1 ≡ t2} (γ : e1 ≡ e2)
  (u : (ω : A') → B ω t1) (ω : A')
  → Πcomp {B = B} {e = e1} {f = u}
      {g = subst (λ t → (ω' : A') → B ω' t) e2 u}
      (cong (λ e → subst (λ t → (ω' : A') → B ω' t) e u) γ) ω
    ≡ cong (λ e → subst (B ω) e (u ω)) γ ∙ sym (noiseΠ {B = B} e2 u ω)
Πcomp-cong-subst {A' = A'} {T = T} {B = B} {t1 = t1} {t2 = t2} {e1 = e1} γ u ω =
  J (λ e2 γ → Πcomp {B = B} {e = e1} {f = u}
                {g = subst (λ t → (ω' : A') → B ω' t) e2 u}
                (cong (λ e → subst (λ t → (ω' : A') → B ω' t) e u) γ) ω
              ≡ cong (λ e → subst (B ω) e (u ω)) γ
                ∙ sym (noiseΠ {B = B} e2 u ω))
    (baseE t2 e1)
    γ
  where
  baseE : (t2' : T) (e : t1 ≡ t2')
          → Πcomp {B = B} {e = e} {f = u}
              {g = subst (λ t → (ω' : A') → B ω' t) e u}
              (refl {x = subst (λ t → (ω' : A') → B ω' t) e u}) ω
            ≡ refl ∙ sym (noiseΠ {B = B} e u ω)
  baseE t2' e =
    J (λ t2' e → Πcomp {B = B} {e = e} {f = u}
                  {g = subst (λ t → (ω' : A') → B ω' t) e u}
                  (refl {x = subst (λ t → (ω' : A') → B ω' t) e u}) ω
                ≡ refl ∙ sym (noiseΠ {B = B} e u ω))
      ( Πcomp-refl {B = B}
          {f = u} {g = subst (λ t → (ω' : A') → B ω' t) refl u}
          (refl {x = subst (λ t → (ω' : A') → B ω' t) refl u}) ω
        ∙ sym (rUnit (sym (noiseΠ {B = B} refl u ω)))
        ∙ lUnit (sym (noiseΠ {B = B} refl u ω)) )
      e

------------------------------------------------------------------------
-- Aliases (stable names for this file's telescopes) of the two
-- ⊙-computation laws Πcomp-⊙ consumes.  With the algebraic ⊙
-- (substComposite ∙ cong (subst P p') q ∙ q'), the re-indexing 2-path
-- at p = p' = refl is just rUnit refl and the computation law is
-- GpdLemmas' sigT-trans-eq-refl verbatim.
------------------------------------------------------------------------

-- The 2-path refl ≡ refl ∙ refl along which ⊙ re-indexes at
-- p = p' = refl (it does not depend on q, q'; the arguments are kept
-- so call sites can name the instance they mean).
⊙-reflSquare′ : {A : Set ℓ} {P : A → Set ℓ'} {x : A} {u v w : P x}
               (q : subst P refl u ≡ v) (q' : subst P refl v ≡ w)
               → refl {x = x} ≡ refl ∙ refl
⊙-reflSquare′ q q' = rUnit refl

sigT-trans-eq-refl′ : {A : Set ℓ} {P : A → Set ℓ'} {x : A} {u v w : P x}
                     (q : subst P refl u ≡ v) (q' : subst P refl v ≡ w)
                     → _⊙_ {P = P} {p = refl} q {p' = refl} q'
                       ≡ cong (λ e → subst P e u)
                              (sym (⊙-reflSquare′ {P = P} q q'))
                         ∙ q ∙ sym (substRefl P v) ∙ q'
sigT-trans-eq-refl′ {P = P} q q' = sigT-trans-eq-refl {P = P} q q'


-- Groupoid mini-kit for the telescopes below.

conj-cancelL : {A : Set ℓ} {x y z : A} (n : x ≡ y) (a : y ≡ z)
               → sym n ∙ (n ∙ a) ≡ a
conj-cancelL n a =
  sym (∙-assoc (sym n) n a) ∙ cong (_∙ a) (lCancel n) ∙ sym (lUnit a)

∙-cong : {A : Set ℓ} {x y z : A} {a a' : x ≡ y} {b b' : y ≡ z}
         → a ≡ a' → b ≡ b' → a ∙ b ≡ a' ∙ b'
∙-cong α β = cong₂ _∙_ α β

-- funExt⁻ of a layer path over refl, unconjugated (inverse reading of
-- Πcomp-refl).

Πcomp-unconj : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {t1 : T} {f g : (ω : A') → B ω t1}
  (X : subst (λ t → (ω : A') → B ω t) (refl {x = t1}) f ≡ g) (ω : A')
  → funExt⁻ {f = subst (λ t → (ω' : A') → B ω' t) refl f} {g = g} X ω
    ≡ noiseΠ {B = B} refl f ω ∙ Πcomp {B = B} {e = refl} {f = f} {g = g} X ω
Πcomp-unconj {A' = A'} {B = B} {t1 = t1} {f = f} {g = g} X ω =
  lUnit fX
  ∙ cong (_∙ fX) (sym (rCancel (noiseΠ {B = B} refl f ω)))
  ∙ ∙-assoc (noiseΠ {B = B} refl f ω) (sym (noiseΠ {B = B} refl f ω)) fX
  ∙ cong (noiseΠ {B = B} refl f ω ∙_)
         (sym (Πcomp-refl {B = B} {f = f} {g = g} X ω))
  where
  fX : subst (λ t → (ω' : A') → B ω' t) refl f ω ≡ g ω
  fX = funExt⁻ {f = subst (λ t → (ω' : A') → B ω' t) refl f} {g = g} X ω

-- Πcomp past ⊙ (Rocq's nth_dpath_trans): the index 2-cells of the two
-- ⊙'s agree definitionally (fst of a Σ-hcomp computes componentwise),
-- so after sigT-trans-eq-refl on both sides only the noiseΠ
-- conjugators remain, and they telescope away.

Πcomp-⊙ : {A' : Set ℓ} {T : Set ℓ'} {B : A' → T → Set ℓ''}
  {x y z : T} {p : x ≡ y} {p' : y ≡ z}
  {u : (ω : A') → B ω x} {v : (ω : A') → B ω y} {w : (ω : A') → B ω z}
  (X : subst (λ t → (ω : A') → B ω t) p u ≡ v)
  (Y : subst (λ t → (ω : A') → B ω t) p' v ≡ w)
  (ω : A')
  → Πcomp {B = B} {e = p ∙ p'} {f = u} {g = w}
      (_⊙_ {P = λ t → (ω' : A') → B ω' t} {u = u} {v = v} {w = w}
           {p = p} X {p' = p'} Y) ω
    ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
        {p = p} (Πcomp {B = B} {e = p} {f = u} {g = v} X ω)
        {p' = p'} (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω)
Πcomp-⊙ {A' = A'} {T = T} {B = B} {x = x} {y = y} {z = z} {p = p}
        {p' = p'} {u = u} {v = v} {w = w} X Y ω =
  J (λ y p → (v : (ω' : A') → B ω' y)
             (X : subst (λ t → (ω' : A') → B ω' t) p u ≡ v)
             (z : T) (p' : y ≡ z) (w : (ω' : A') → B ω' z)
             (Y : subst (λ t → (ω' : A') → B ω' t) p' v ≡ w)
             → Πcomp {B = B} {e = p ∙ p'} {f = u} {g = w}
                 (_⊙_ {P = λ t → (ω' : A') → B ω' t} {u = u} {v = v}
                      {w = w} {p = p} X {p' = p'} Y) ω
               ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
                   {p = p} (Πcomp {B = B} {e = p} {f = u} {g = v} X ω)
                   {p' = p'} (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω))
    (λ v X z p' w Y →
      J (λ z p' → (w : (ω' : A') → B ω' z)
                  (Y : subst (λ t → (ω' : A') → B ω' t) p' v ≡ w)
                  → Πcomp {B = B} {e = refl ∙ p'} {f = u} {g = w}
                      (_⊙_ {P = λ t → (ω' : A') → B ω' t} {u = u} {v = v}
                           {w = w} {p = refl} X {p' = p'} Y) ω
                    ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
                        {p = refl}
                        (Πcomp {B = B} {e = refl} {f = u} {g = v} X ω)
                        {p' = p'}
                        (Πcomp {B = B} {e = p'} {f = v} {g = w} Y ω))
        (λ w Y → base v X w Y)
        p' w Y)
    p v X z p' w Y
  where
  L : T → Set _
  L t = (ω' : A') → B ω' t

  base : (v : (ω' : A') → B ω' x)
         (X : subst L (refl {x = x}) u ≡ v)
         (w : (ω' : A') → B ω' x)
         (Y : subst L (refl {x = x}) v ≡ w)
         → Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w}
             (_⊙_ {P = L} {u = u} {v = v} {w = w}
                  {p = refl} X {p' = refl} Y) ω
           ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
               {p = refl} (Πcomp {B = B} {e = refl} {f = u} {g = v} X ω)
               {p' = refl} (Πcomp {B = B} {e = refl} {f = v} {g = w} Y ω)
  base v X w Y = b1 ∙ b2 ∙ b3 ∙ tele ∙ b5
    where
    nU nV : _
    nU = noiseΠ {B = B} refl u ω
    nV = noiseΠ {B = B} refl v ω
    N1v : subst L refl v ω ≡ v ω
    N1v = funExt⁻ (transportRefl v) ω
    N2v : subst (B ω) refl (v ω) ≡ v ω
    N2v = transportRefl (v ω)
    ΠcX = Πcomp {B = B} {e = refl} {f = u} {g = v} X ω
    ΠcY = Πcomp {B = B} {e = refl} {f = v} {g = w} Y ω
    cL : subst L (refl ∙ refl) u ≡ subst L refl u
    cL = cong (λ e → subst L e u)
              (sym (⊙-reflSquare′ {P = L} {u = u} {v = v} {w = w} X Y))
    cB : subst (B ω) (refl ∙ refl) (u ω) ≡ subst (B ω) refl (u ω)
    cB = cong (λ e → subst (B ω) e (u ω))
              (sym (⊙-reflSquare′ {P = L} {u = u} {v = v} {w = w} X Y))
    RST : subst L refl u ≡ w
    RST = X ∙ sym (substRefl L v) ∙ Y

    b1 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w}
           (_⊙_ {P = L} {u = u} {v = v} {w = w}
                {p = refl} X {p' = refl} Y) ω
         ≡ Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w} (cL ∙ RST) ω
    b1 = cong (λ q → Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w} q ω)
              (sigT-trans-eq-refl′ {P = L} {u = u} {v = v} {w = w} X Y)

    b2 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = w} (cL ∙ RST) ω
         ≡ Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = subst L refl u}
             cL ω
           ∙ funExt⁻ RST ω
    b2 = Πcomp-∙ {B = B} {e = refl ∙ refl} {f = u}
           {g = subst L refl u} {h = w} cL RST ω

    id1 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = subst L refl u}
            cL ω
          ≡ cB ∙ sym nU
    id1 = Πcomp-cong-subst {B = B}
            (sym (⊙-reflSquare′ {P = L} {u = u} {v = v} {w = w} X Y)) u ω

    id2 : funExt⁻ X ω ≡ nU ∙ ΠcX
    id2 = Πcomp-unconj {B = B} {f = u} {g = v} X ω

    id3 : funExt⁻ {B = λ ω' → B ω' x} {f = v} {g = subst L refl v}
            (sym (substRefl L v)) ω
          ≡ sym N2v ∙ sym nV
    id3 = sym (cong (sym N2v ∙_)
                    (cong sym (noiseΠ-refl {B = B} v ω)
                     ∙ symDistr N1v (sym N2v))
               ∙ conj-cancelL N2v (sym N1v))

    id4 : funExt⁻ Y ω ≡ nV ∙ ΠcY
    id4 = Πcomp-unconj {B = B} {f = v} {g = w} Y ω

    b3 : Πcomp {B = B} {e = refl ∙ refl} {f = u} {g = subst L refl u}
           cL ω
         ∙ funExt⁻ RST ω
         ≡ (cB ∙ sym nU)
           ∙ ((nU ∙ ΠcX) ∙ ((sym N2v ∙ sym nV) ∙ (nV ∙ ΠcY)))
    b3 = ∙-cong {x = subst (B ω) (refl ∙ refl) (u ω)}
           {y = subst L refl u ω} {z = w ω}
           id1
           (∙-cong {x = subst L refl u ω} {y = v ω} {z = w ω}
             id2
             (∙-cong {x = v ω} {y = subst L refl v ω} {z = w ω}
               id3 id4))

    tele : (cB ∙ sym nU)
           ∙ ((nU ∙ ΠcX) ∙ ((sym N2v ∙ sym nV) ∙ (nV ∙ ΠcY)))
           ≡ cB ∙ (ΠcX ∙ (sym N2v ∙ ΠcY))
    tele =
      cong (λ C' → (cB ∙ sym nU) ∙ ((nU ∙ ΠcX) ∙ C'))
           (∙-assoc (sym N2v) (sym nV) (nV ∙ ΠcY)
            ∙ cong (sym N2v ∙_) (conj-cancelL nV ΠcY))
      ∙ cong ((cB ∙ sym nU) ∙_)
             (∙-assoc nU ΠcX (sym N2v ∙ ΠcY))
      ∙ ∙-assoc cB (sym nU) (nU ∙ (ΠcX ∙ (sym N2v ∙ ΠcY)))
      ∙ cong (cB ∙_) (conj-cancelL nU (ΠcX ∙ (sym N2v ∙ ΠcY)))

    b5 : cB ∙ (ΠcX ∙ (sym N2v ∙ ΠcY))
         ≡ _⊙_ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
             {p = refl} ΠcX {p' = refl} ΠcY
    b5 = sym (sigT-trans-eq-refl′ {P = B ω} {u = u ω} {v = v ω} {w = w ω}
               ΠcX ΠcY)
