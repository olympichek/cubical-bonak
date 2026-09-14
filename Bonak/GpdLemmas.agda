------------------------------------------------------------------------
-- Bonak.GpdLemmas — the PathP kit one storey up, for the νGpd tower's
-- 2-dimensional coherences.
--
-- The νGpd tower states its coh2 coherences as dependent squares over
-- the 2-dimensional frame coherence, so the kit is: dependent squares
-- (SquareP), the comp′ filler (fill′, what hfill is to hcomp′), the
-- filler form of the layer-coherence square (cohLayer-fillP — the
-- interior of Bonak.RewLemmas' cohLayer-squareP, which the painting
-- 2-coherence's s = 0 clause is), and cube filling in a groupoid
-- (isGroupoid→Cube — the storey's single truncation principle).
------------------------------------------------------------------------

module Bonak.GpdLemmas where

open import Bonak.Prelude
open import Bonak.RewLemmas

private variable
  ℓ : Level

-- The comp′ filler: fill′ A u u0 i1 is comp′ A u u0, fill′ A u u0 i0
-- is u0.
fill′ : (A : I → Set ℓ) {φ : I} (u : (i : I) → Partial φ (A i))
        (u0 : Sub (A i0) φ (u i0)) (i : I) → A i
fill′ A {φ} u u0 i =
  comp′ (λ j → A (i ∧ j))
        (λ j → λ { (φ = i1) → u (i ∧ j) itIsOne
                 ; (i = i0) → outS u0 })
        (outS u0)

-- Squares over a binary family (the 2-dimensional PathP).
SquareP : (A : I → I → Set ℓ)
          {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
          (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
          {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
          (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
          (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀)
          (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁) → Set ℓ
SquareP A a₀₋ a₁₋ a₋₀ a₋₁ =
  PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

-- The filler of RewLemmas' compPathP, in its composition direction.
compPathP-filler : {ℓ ℓ' : Level} {A : Set ℓ} {P : A → Set ℓ'}
  {x y z : A} {p : x ≡ y} {q : y ≡ z}
  {u : P x} {v : P y} {w : P z}
  (α : PathP (λ i → P (p i)) u v) (β : PathP (λ i → P (q i)) v w)
  (j i : I) → P (compPath-filler p q j i)
compPathP-filler {P = P} {p = p} {q = q} {u = u} α β j i =
  fill′ (λ j' → P (compPath-filler p q j' i))
        (λ j' → λ { (i = i0) → u ; (i = i1) → β j' })
        (inS (α i)) j

------------------------------------------------------------------------
-- Dependent composition of pairs.
------------------------------------------------------------------------

-- The doubly dependent composite: paths in a second-storey family,
-- composed over a base composite and the compPathP of a first-storey
-- pair of paths.
module _ {ℓx ℓl ℓm : Level} {X : Set ℓx} {L : X → Set ℓl}
  {M : (x : X) → L x → Set ℓm}
  {x y z : X} {p : x ≡ y} {q : y ≡ z}
  {fx : L x} {fy : L y} {fz : L z}
  (f₁ : PathP (λ i → L (p i)) fx fy) (f₂ : PathP (λ i → L (q i)) fy fz)
  {u : M x fx} {v : M y fy} {w : M z fz}
  (g₁ : PathP (λ i → M (p i) (f₁ i)) u v)
  (g₂ : PathP (λ i → M (q i) (f₂ i)) v w)
  where

  compPathPᵈ-fill : (j i : I)
    → M (compPath-filler p q j i) (compPathP-filler {P = L} f₁ f₂ j i)
  compPathPᵈ-fill j i =
    fill′ (λ j' → M (compPath-filler p q j' i)
                    (compPathP-filler {P = L} f₁ f₂ j' i))
          (λ j' → λ { (i = i0) → u ; (i = i1) → g₂ j' })
          (inS (g₁ i)) j

  compPathPᵈ : PathP (λ i → M ((p ∙ q) i) (compPathP {P = L} f₁ f₂ i))
                 u w
  compPathPᵈ i = compPathPᵈ-fill i1 i

  -- Pairing vs composition, one storey up: the compPathP of two
  -- pairings against the pairing of compPathP and compPathPᵈ.
  compPathP-pairΣ :
    PathP (λ m → PathP (λ i → Σ (L ((p ∙ q) i)) (M ((p ∙ q) i)))
             (fx , u) (fz , w))
      (compPathP {P = λ x' → Σ (L x') (M x')}
         (λ i → (f₁ i , g₁ i)) (λ i → (f₂ i , g₂ i)))
      (λ i → ( compPathP {P = L} f₁ f₂ i , compPathPᵈ i ))
  compPathP-pairΣ m i =
    comp′ (λ j → Σ (L (compPath-filler p q j i))
                   (M (compPath-filler p q j i)))
          (λ j → λ { (i = i0) → (fx , u)
                   ; (i = i1) → (f₂ j , g₂ j)
                   ; (m = i1) → ( compPathP-filler {P = L} f₁ f₂ j i
                                , compPathPᵈ-fill j i ) })
          ((f₁ i , g₁ i))

-- Application of a composite in a Π-family of restrictions at a fixed
-- argument, against the pointwise composite of the applications: comp
-- in a Π-type evaluates through the function direction, so the two
-- are different terms — the Π-analogue of the pairing-vs-composition
-- squares above. The base square simultaneously connects the
-- composite of the restricted base paths to the restriction of their
-- composite, which likewise differ (cong does not distribute over ∙
-- definitionally), so one cell corrects base and fiber together.
module ∙Πapp {ℓa ℓt ℓx ℓp : Level} {A : Set ℓa} {T : Set ℓt}
  {X : Set ℓx} {P : X → Set ℓp} (R : A → T → X)
  {x y z : A} (p : x ≡ y) (q : y ≡ z)
  {u : (t : T) → P (R x t)} {v : (t : T) → P (R y t)}
  {w : (t : T) → P (R z t)}
  (α : PathP (λ i → (t : T) → P (R (p i) t)) u v)
  (β : PathP (λ i → (t : T) → P (R (q i) t)) v w)
  (t : T)
  where

  fill : (j m i : I) → X
  fill j m i =
    hfill (λ j' → λ { (i = i0) → R x t
                    ; (i = i1) → R (q j') t
                    ; (m = i1) → R (compPath-filler p q j' i) t })
          (inS (R (p i) t)) j

  csq : Square ((λ i → R (p i) t) ∙ (λ i → R (q i) t))
          (λ i → R ((p ∙ q) i) t)
          (λ _ → R x t) (λ _ → R z t)
  csq m i = fill i1 m i

  csqP : SquareP (λ m i → P (csq m i))
      (compPathP {P = P} (λ i → α i t) (λ i → β i t))
      (λ i → compPathP {P = λ a → (t' : T) → P (R a t')} α β i t)
      (λ _ → u t) (λ _ → w t)
  csqP m i =
    comp′ (λ j → P (fill j m i))
      (λ j → λ { (i = i0) → u t
               ; (i = i1) → β j t
               ; (m = i1) → compPathP-filler
                              {P = λ a → (t' : T) → P (R a t')}
                              α β j i t })
      (α i t)

-- The non-Π form of the same connection: an application under a map h
-- of a composite against the composite of the applications, together
-- with the fiber square carrying a dependent composite between the two
-- base spellings.
module ∙congF {ℓa ℓx ℓp : Level} {A : Set ℓa}
  {X : Set ℓx} {P : X → Set ℓp} (h : A → X)
  {x y z : A} (p : x ≡ y) (q : y ≡ z)
  where

  fill : (j m i : I) → X
  fill j m i =
    hfill (λ j' → λ { (i = i0) → h x
                    ; (i = i1) → h (q j')
                    ; (m = i1) → h (compPath-filler p q j' i) })
          (inS (h (p i))) j

  csq : Square ((λ i → h (p i)) ∙ (λ i → h (q i)))
          (λ i → h ((p ∙ q) i))
          (λ _ → h x) (λ _ → h z)
  csq m i = fill i1 m i

  module _ {u : P (h x)} {v : P (h y)} {w : P (h z)}
    (α : PathP (λ i → P (h (p i))) u v)
    (β : PathP (λ i → P (h (q i))) v w)
    where

   csqP : SquareP (λ m i → P (csq m i))
       (compPathP {P = P} α β)
       (compPathP {P = λ a → P (h a)} α β)
       (λ _ → u) (λ _ → w)
   csqP m i =
     comp′ (λ j → P (fill j m i))
       (λ j → λ { (i = i0) → u
                ; (i = i1) → β j
                ; (m = i1) → compPathP-filler
                               {P = λ a → P (h a)} α β j i })
       (α i)

------------------------------------------------------------------------
-- A dependent square of pairs over X. Its interior pairs Lsq and Csq;
-- the two composite faces require the dependent pairing comparison.
------------------------------------------------------------------------

module Σ≡hex {ℓa ℓb : Level} {A : Set ℓa} {B : A → Set ℓb}
  -- the a₋₀ face's two factors
  {xc yc zc : A} (a₁ : xc ≡ yc) (a₂ : yc ≡ zc)
  {uc : B xc} {vc : B yc} {wc : B zc}
  (b₁ : PathP (λ i → B (a₁ i)) uc vc) (b₂ : PathP (λ i → B (a₂ i)) vc wc)
  -- the a₋₁ face's two factors
  {xd yd zd : A} (a₁' : xd ≡ yd) (a₂' : yd ≡ zd)
  {ud : B xd} {vd : B yd} {wd : B zd}
  (b₁' : PathP (λ i → B (a₁' i)) ud vd)
  (b₂' : PathP (λ i → B (a₂' i)) vd wd)
  -- the two single-cell faces (a₀₋ and a₁₋)
  (kA : xc ≡ xd) (kB : PathP (λ j → B (kA j)) uc ud)
  (e1A : zc ≡ zd) (e1B : PathP (λ j → B (e1A j)) wc wd)
  -- the square of first components and the square over it
  (X : Square kA e1A (a₁ ∙ a₂) (a₁' ∙ a₂'))
  (Lsq : SquareP (λ i j → B (X i j)) kB e1B
           (compPathP {P = B} b₁ b₂) (compPathP {P = B} b₁' b₂'))
  where

  -- The second-storey square lies over the pointwise pair of X and Lsq.
  module Dep {ℓm : Level} {M : Σ A B → Set ℓm}
    {muc : M (xc , uc)} {mvc : M (yc , vc)} {mwc : M (zc , wc)}
    (g₁ : PathP (λ i → M (a₁ i , b₁ i)) muc mvc)
    (g₂ : PathP (λ i → M (a₂ i , b₂ i)) mvc mwc)
    {mud : M (xd , ud)} {mvd : M (yd , vd)} {mwd : M (zd , wd)}
    (g₁' : PathP (λ i → M (a₁' i , b₁' i)) mud mvd)
    (g₂' : PathP (λ i → M (a₂' i , b₂' i)) mvd mwd)
    (gK : PathP (λ j → M (kA j , kB j)) muc mud)
    (gE1 : PathP (λ j → M (e1A j , e1B j)) mwc mwd)
    (Csq : SquareP (λ i j → M (X i j , Lsq i j)) gK gE1
             (compPathP {P = M} g₁ g₂) (compPathP {P = M} g₁' g₂'))
    where

    private
      face₀ : (j : I) → Σ (B (X i0 j)) (λ b → M (X i0 j , b))
      face₀ j = (kB j , gK j)
      face₁ : (j : I) → Σ (B (X i1 j)) (λ b → M (X i1 j , b))
      face₁ j = (e1B j , gE1 j)

    hexᵈ : SquareP (λ i j → Σ (B (X i j)) (λ b → M (X i j , b)))
        (λ j → face₀ j) (λ j → face₁ j)
        (compPathP {P = λ x → Σ (B x) (λ b → M (x , b))}
           (λ i → (b₁ i , g₁ i)) (λ i → (b₂ i , g₂ i)))
        (compPathP {P = λ x → Σ (B x) (λ b → M (x , b))}
           (λ i → (b₁' i , g₁' i)) (λ i → (b₂' i , g₂' i)))
    hexᵈ i j =
      hcomp′ (λ m → λ
        { (i = i0) → face₀ j
        ; (i = i1) → face₁ j
        ; (j = i0) → compPathP-pairΣ {L = B} {M = λ x b → M (x , b)}
                       b₁ b₂ g₁ g₂ (~ m) i
        ; (j = i1) → compPathP-pairΣ {L = B} {M = λ x b → M (x , b)}
                       b₁' b₂' g₁' g₂' (~ m) i })
        (Lsq i j , Csq i j)

------------------------------------------------------------------------
-- The pasting kit for the layer 2-coherence: vertical composition of
-- squares and of dependent squares over them, the functoriality filler
-- of a two-argument application over a composite, and pointwise
-- composition of connection squares. All are Kan fillings — no
-- truncation.
------------------------------------------------------------------------

-- Vertical composition (in the first square direction), with
-- compPath / compPathP side edges.
module _ {ℓ : Level} {X : Set ℓ}
  {x₀₀ x₀₁ x₁₀ x₁₁ x₂₀ x₂₁ : X}
  {top : x₀₀ ≡ x₀₁} {mid : x₁₀ ≡ x₁₁} {bot : x₂₀ ≡ x₂₁}
  {c₁ : x₀₀ ≡ x₁₀} {d₁ : x₀₁ ≡ x₁₁} {c₂ : x₁₀ ≡ x₂₀} {d₂ : x₁₁ ≡ x₂₁}
  (B₁ : Square top mid c₁ d₁) (B₂ : Square mid bot c₂ d₂)
  where

  ∙v-fill : (o m j : I) → X
  ∙v-fill o m j =
    hfill (λ o' → λ { (m = i0) → top j
                    ; (m = i1) → B₂ o' j
                    ; (j = i0) → compPath-filler c₁ c₂ o' m
                    ; (j = i1) → compPath-filler d₁ d₂ o' m })
          (inS (B₁ m j)) o

  ∙v : Square top bot (c₁ ∙ c₂) (d₁ ∙ d₂)
  ∙v m j = ∙v-fill i1 m j

module _ {ℓ ℓ' : Level} {X : Set ℓ} {P : X → Set ℓ'}
  {x₀₀ x₀₁ x₁₀ x₁₁ x₂₀ x₂₁ : X}
  {top : x₀₀ ≡ x₀₁} {mid : x₁₀ ≡ x₁₁} {bot : x₂₀ ≡ x₂₁}
  {c₁ : x₀₀ ≡ x₁₀} {d₁ : x₀₁ ≡ x₁₁} {c₂ : x₁₀ ≡ x₂₀} {d₂ : x₁₁ ≡ x₂₁}
  {B₁ : Square top mid c₁ d₁} {B₂ : Square mid bot c₂ d₂}
  {ftop₀ : P x₀₀} {ftop₁ : P x₀₁} {fmid₀ : P x₁₀} {fmid₁ : P x₁₁}
  {fbot₀ : P x₂₀} {fbot₁ : P x₂₁}
  {ftop : PathP (λ j → P (top j)) ftop₀ ftop₁}
  {fmid : PathP (λ j → P (mid j)) fmid₀ fmid₁}
  {fbot : PathP (λ j → P (bot j)) fbot₀ fbot₁}
  {γ₁ : PathP (λ m → P (c₁ m)) ftop₀ fmid₀}
  {δ₁ : PathP (λ m → P (d₁ m)) ftop₁ fmid₁}
  {γ₂ : PathP (λ m → P (c₂ m)) fmid₀ fbot₀}
  {δ₂ : PathP (λ m → P (d₂ m)) fmid₁ fbot₁}
  (σ₁ : SquareP (λ m j → P (B₁ m j)) ftop fmid γ₁ δ₁)
  (σ₂ : SquareP (λ m j → P (B₂ m j)) fmid fbot γ₂ δ₂)
  where

  ∙vP : SquareP (λ m j → P (∙v B₁ B₂ m j)) ftop fbot
          (compPathP {P = P} γ₁ γ₂) (compPathP {P = P} δ₁ δ₂)
  ∙vP m j =
    comp′ (λ o → P (∙v-fill B₁ B₂ o m j))
      (λ o → λ { (m = i0) → ftop j
               ; (m = i1) → σ₂ o j
               ; (j = i0) → compPathP-filler {P = P} γ₁ γ₂ o m
               ; (j = i1) → compPathP-filler {P = P} δ₁ δ₂ o m })
      (σ₁ m j)

-- Functoriality of a two-argument application over a composite: the
-- application along the composed pair against the composite of the
-- applications, as a square with degenerate side edges.
cong²Funct : {ℓx ℓs ℓw : Level} {X : Set ℓx} {S : X → Set ℓs}
  {W : X → Set ℓw} (h : (x : X) → S x → W x)
  {x y z : X} {p : x ≡ y} {q : y ≡ z}
  {u : S x} {v : S y} {w' : S z}
  (sp : PathP (λ i → S (p i)) u v) (sq : PathP (λ i → S (q i)) v w')
  → SquareP (λ m i → W ((p ∙ q) i))
      (λ i → h ((p ∙ q) i) (compPathP {P = S} sp sq i))
      (compPathP {P = W} (λ i → h (p i) (sp i)) (λ i → h (q i) (sq i)))
      (λ _ → h x u) (λ _ → h z w')
cong²Funct {S = S} {W = W} h {x = x} {p = p} {q = q} {u = u} sp sq m i =
  comp′ (λ j' → W (compPath-filler p q j' i))
    (λ j' → λ { (i = i0) → h x u
              ; (i = i1) → h (q j') (sq j')
              ; (m = i0) → h (compPath-filler p q j' i)
                             (compPathP-filler {P = S} sp sq j' i) })
    (h (p i) (sp i))

-- Pointwise composition of two connection squares: at each stage m the
-- compPathP of the two slices, over the pointwise composite of the base
-- slices. The i0 side edge of the result is the first square's — the
-- composite's comp′ keeps its (i = i0) branch there.
module _ {ℓ : Level} {X : Set ℓ}
  {xu₀ xu₁ xm₀ xm₁ xv₀ xv₁ : X}
  {U₀ : xu₀ ≡ xm₀} {U₁ : xu₁ ≡ xm₁}
  {V₀ : xm₀ ≡ xv₀} {V₁ : xm₁ ≡ xv₁}
  {γS : xu₀ ≡ xu₁} {γM : xm₀ ≡ xm₁} {γE : xv₀ ≡ xv₁}
  (U : Square U₀ U₁ γS γM) (V : Square V₀ V₁ γM γE)
  where

  ∙slice : Square (U₀ ∙ V₀) (U₁ ∙ V₁) γS γE
  ∙slice m i = ((λ i' → U m i') ∙ (λ i' → V m i')) i

module _ {ℓ ℓ' : Level} {X : Set ℓ} {P : X → Set ℓ'}
  {xu₀ xu₁ xm₀ xm₁ xv₀ xv₁ : X}
  {U₀ : xu₀ ≡ xm₀} {U₁ : xu₁ ≡ xm₁}
  {V₀ : xm₀ ≡ xv₀} {V₁ : xm₁ ≡ xv₁}
  {γS : xu₀ ≡ xu₁} {γM : xm₀ ≡ xm₁} {γE : xv₀ ≡ xv₁}
  {U : Square U₀ U₁ γS γM} {V : Square V₀ V₁ γM γE}
  {fu₀ : P xu₀} {fu₁ : P xu₁} {fm₀ : P xm₀} {fm₁ : P xm₁}
  {fv₀ : P xv₀} {fv₁ : P xv₁}
  {α₀ : PathP (λ i → P (U₀ i)) fu₀ fm₀}
  {α₁ : PathP (λ i → P (U₁ i)) fu₁ fm₁}
  {β₀ : PathP (λ i → P (V₀ i)) fm₀ fv₀}
  {β₁ : PathP (λ i → P (V₁ i)) fm₁ fv₁}
  {gS : PathP (λ m → P (γS m)) fu₀ fu₁}
  {gM : PathP (λ m → P (γM m)) fm₀ fm₁}
  {gE : PathP (λ m → P (γE m)) fv₀ fv₁}
  (σ : SquareP (λ m i → P (U m i)) α₀ α₁ gS gM)
  (τ : SquareP (λ m i → P (V m i)) β₀ β₁ gM gE)
  where

  ∙sliceP : SquareP (λ m i → P (∙slice U V m i))
      (compPathP {P = P} α₀ β₀) (compPathP {P = P} α₁ β₁) gS gE
  ∙sliceP m i =
    comp′ (λ j' → P (compPath-filler (λ i' → U m i')
                       (λ i' → V m i') j' i))
      (λ j' → λ { (i = i0) → gS m ; (i = i1) → τ m j' })
      (σ m i)


-- The left composition filler, and its dependent version.
compPath-filler' : {ℓ' : Level} {A : Set ℓ'} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) → PathP (λ j → p (~ j) ≡ z) q (p ∙ q)
compPath-filler' {x = x} p q j i =
  hcomp′ (λ k → λ { (i = i0) → p (~ j)
                  ; (i = i1) → q k
                  ; (j = i0) → q (i ∧ k) })
         (p (i ∨ ~ j))

compPath-filler'-fill : {ℓ' : Level} {A : Set ℓ'} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) (k j i : I) → A
compPath-filler'-fill {x = x} p q k j i =
  hfill (λ k' → λ { (i = i0) → p (~ j)
                  ; (i = i1) → q k'
                  ; (j = i0) → q (i ∧ k') })
        (inS (p (i ∨ ~ j))) k

compPathP-filler' : {ℓ' ℓ'' : Level} {A : Set ℓ'} {P : A → Set ℓ''}
  {x y z : A} {p : x ≡ y} {q : y ≡ z}
  {u : P x} {v : P y} {w : P z}
  (α : PathP (λ i → P (p i)) u v) (β : PathP (λ i → P (q i)) v w)
  → PathP (λ j → PathP (λ i → P (compPath-filler' p q j i))
             (α (~ j)) w)
      β (compPathP {P = P} α β)
compPathP-filler' {P = P} {p = p} {q = q} α β j i =
  comp′ (λ k → P (compPath-filler'-fill p q k j i))
    (λ k → λ { (i = i0) → α (~ j)
             ; (i = i1) → β k
             ; (j = i0) → β (i ∧ k) })
    (α (i ∨ ~ j))

-- The associativity cell, base and dependent, with degenerate side
-- edges.
module _ {ℓ' : Level} {A : Set ℓ'} {w x y z : A}
  (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  where

  assocSq-fill : (k m i : I) → A
  assocSq-fill k m i =
    hfill (λ k' → λ { (i = i0) → w
                    ; (i = i1) → compPath-filler' q r m k' })
          (inS (compPath-filler p q (~ m) i)) k

  assocSq : Square ((p ∙ q) ∙ r) (p ∙ (q ∙ r)) (λ _ → w) (λ _ → z)
  assocSq m i = assocSq-fill i1 m i

module _ {ℓ' ℓ'' : Level} {A : Set ℓ'} {P : A → Set ℓ''}
  {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z}
  {fw : P w} {fx : P x} {fy : P y} {fz : P z}
  (a : PathP (λ i → P (p i)) fw fx) (b : PathP (λ i → P (q i)) fx fy)
  (c : PathP (λ i → P (r i)) fy fz)
  where

  assocP : SquareP (λ m i → P (assocSq p q r m i))
      (compPathP {P = P} (compPathP {P = P} a b) c)
      (compPathP {P = P} a (compPathP {P = P} b c))
      (λ _ → fw) (λ _ → fz)
  assocP m i =
    comp′ (λ k → P (assocSq-fill p q r k m i))
      (λ k → λ { (i = i0) → fw
               ; (i = i1) → compPathP-filler' {P = P} b c m k })
      (compPathP-filler {P = P} a b (~ m) i)

-- Vertical composition of cells with degenerate side edges, keeping
-- them degenerate (unlike ∙v, whose side edges compose).
module _ {ℓ' : Level} {X : Set ℓ'} {x₀ x₁ : X}
  {r₁ r₂ r₃ : x₀ ≡ x₁}
  (BC₁ : Square r₁ r₂ (λ _ → x₀) (λ _ → x₁))
  (BC₂ : Square r₂ r₃ (λ _ → x₀) (λ _ → x₁))
  where

  ∙r-fill : (o' o m : I) → X
  ∙r-fill o' o m =
    hfill (λ o'' → λ { (o = i0) → r₁ m
                     ; (o = i1) → BC₂ o'' m
                     ; (m = i0) → x₀
                     ; (m = i1) → x₁ })
          (inS (BC₁ o m)) o'

  ∙r : Square r₁ r₃ (λ _ → x₀) (λ _ → x₁)
  ∙r o m = ∙r-fill i1 o m

module _ {ℓ' ℓ'' : Level} {X : Set ℓ'} {P : X → Set ℓ''}
  {x₀ x₁ : X} {r₁ r₂ r₃ : x₀ ≡ x₁}
  {BC₁ : Square r₁ r₂ (λ _ → x₀) (λ _ → x₁)}
  {BC₂ : Square r₂ r₃ (λ _ → x₀) (λ _ → x₁)}
  {f₀ : P x₀} {f₁ : P x₁}
  {ρ₁ : PathP (λ m → P (r₁ m)) f₀ f₁}
  {ρ₂ : PathP (λ m → P (r₂ m)) f₀ f₁}
  {ρ₃ : PathP (λ m → P (r₃ m)) f₀ f₁}
  (C₁ : SquareP (λ o m → P (BC₁ o m)) ρ₁ ρ₂ (λ _ → f₀) (λ _ → f₁))
  (C₂ : SquareP (λ o m → P (BC₂ o m)) ρ₂ ρ₃ (λ _ → f₀) (λ _ → f₁))
  where

  ∙rP : SquareP (λ o m → P (∙r BC₁ BC₂ o m)) ρ₁ ρ₃
          (λ _ → f₀) (λ _ → f₁)
  ∙rP o m =
    comp′ (λ o' → P (∙r-fill BC₁ BC₂ o' o m))
      (λ o' → λ { (o = i0) → ρ₁ m
                ; (o = i1) → C₂ o' m
                ; (m = i0) → f₀
                ; (m = i1) → f₁ })
      (C₁ o m)

-- Padding a dependent square's two side edges by cells with degenerate
-- side edges, keeping the two end faces.
module _ {ℓ' : Level} {X : Set ℓ'}
  {b₀₀ b₀₁ b₁₀ b₁₁ : X}
  {bA₀ : b₀₀ ≡ b₀₁} {bA₁ : b₁₀ ≡ b₁₁}
  {bL bL' : b₀₀ ≡ b₁₀} {bR bR' : b₀₁ ≡ b₁₁}
  (BG : Square bA₀ bA₁ bL bR)
  (BCL : Square bL bL' (λ _ → b₀₀) (λ _ → b₁₀))
  (BCR : Square bR bR' (λ _ → b₀₁) (λ _ → b₁₁))
  where

  pad-fill : (o m i : I) → X
  pad-fill o m i =
    hfill (λ o' → λ { (i = i0) → BCL o' m
                    ; (i = i1) → BCR o' m
                    ; (m = i0) → bA₀ i
                    ; (m = i1) → bA₁ i })
          (inS (BG m i)) o

  pad : Square bA₀ bA₁ bL' bR'
  pad m i = pad-fill i1 m i

module _ {ℓ' ℓ'' : Level} {X : Set ℓ'} {P : X → Set ℓ''}
  {b₀₀ b₀₁ b₁₀ b₁₁ : X}
  {bA₀ : b₀₀ ≡ b₀₁} {bA₁ : b₁₀ ≡ b₁₁}
  {bL bL' : b₀₀ ≡ b₁₀} {bR bR' : b₀₁ ≡ b₁₁}
  {BG : Square bA₀ bA₁ bL bR}
  {BCL : Square bL bL' (λ _ → b₀₀) (λ _ → b₁₀)}
  {BCR : Square bR bR' (λ _ → b₀₁) (λ _ → b₁₁)}
  {f₀₀ : P b₀₀} {f₀₁ : P b₀₁} {f₁₀ : P b₁₀} {f₁₁ : P b₁₁}
  {A₀ : PathP (λ i → P (bA₀ i)) f₀₀ f₀₁}
  {A₁ : PathP (λ i → P (bA₁ i)) f₁₀ f₁₁}
  {gL : PathP (λ m → P (bL m)) f₀₀ f₁₀}
  {gL' : PathP (λ m → P (bL' m)) f₀₀ f₁₀}
  {gR : PathP (λ m → P (bR m)) f₀₁ f₁₁}
  {gR' : PathP (λ m → P (bR' m)) f₀₁ f₁₁}
  (G : SquareP (λ m i → P (BG m i)) A₀ A₁ gL gR)
  (CL : SquareP (λ o m → P (BCL o m)) gL gL' (λ _ → f₀₀) (λ _ → f₁₀))
  (CR : SquareP (λ o m → P (BCR o m)) gR gR' (λ _ → f₀₁) (λ _ → f₁₁))
  where

  padP : SquareP (λ m i → P (pad BG BCL BCR m i)) A₀ A₁ gL' gR'
  padP m i =
    comp′ (λ o → P (pad-fill BG BCL BCR o m i))
      (λ o → λ { (i = i0) → CL o m
               ; (i = i1) → CR o m
               ; (m = i0) → A₀ i
               ; (m = i1) → A₁ i })
      (G m i)

-- The junction cell of the layer 2-coherence's lateral pasting: the
-- composite edge "apply h to the composite, then the transport" carried
-- to the reassociated composite of the applications, as one filler.
-- The interior at fill stage k = i0 is rf of the (reversed) compPath
-- filler of p and q, whose o-edges are rf ((p ∙ q) m) and rf (p m);
-- the m = i1 wall is compPath-filler' (cong rf q) r, whose o-edges
-- are r and cong rf q ∙ r. Composing against that wall makes the
-- o = i0 face literally (cong rf (p ∙ q)) ∙ r and the o = i1 face
-- literally cong rf p ∙ (cong rf q ∙ r), definitionally (hfill at i1
-- is hcomp; compPath-filler' at j = i0 / j = i1 is r / cong rf q ∙ r).
-- cell is the same composition one fiber up; six instances close the
-- six junctions of the cube's two pasted laterals.
module junctionP {ℓa ℓx ℓp : Level} {A : Set ℓa}
  {X : Set ℓx} {P : X → Set ℓp}
  (rf : A → X)
  {x y z : A} (p : x ≡ y) (q : y ≡ z)
  {x1 : X} (r : rf z ≡ x1)
  where

  base-fill : (k o m : I) → X
  base-fill k o m =
    hfill (λ k' → λ { (m = i0) → rf x
                    ; (m = i1) → compPath-filler' (λ i → rf (q i)) r o k' })
          (inS (rf (compPath-filler p q (~ o) m))) k

  base : Square ((λ i → rf ((p ∙ q) i)) ∙ r)
      ((λ m → rf (p m)) ∙ ((λ m → rf (q m)) ∙ r))
      (λ _ → rf x) (λ _ → x1)
  base o m = base-fill i1 o m

  module _ {ℓs : Level} {S : A → Set ℓs}
    (h : (a : A) → S a → P (rf a))
    {u : S x} {v : S y} {w' : S z}
    (sp : PathP (λ i → S (p i)) u v) (sq : PathP (λ i → S (q i)) v w')
    {fw : P x1} (c : PathP (λ m → P (r m)) (h z w') fw)
    where

    private
      hp : PathP (λ m → P (rf (p m))) (h x u) (h y v)
      hp = λ m → h (p m) (sp m)
      hq : PathP (λ m → P (rf (q m))) (h y v) (h z w')
      hq = λ m → h (q m) (sq m)

    cell : SquareP (λ o m → P (base o m))
        (compPathP {P = P}
          (λ i → h ((p ∙ q) i) (compPathP {P = S} sp sq i)) c)
        (compPathP {P = P} hp (compPathP {P = P} hq c))
        (λ _ → h x u) (λ _ → fw)
    cell o m =
      comp′ (λ k → P (base-fill k o m))
        (λ k → λ { (m = i0) → h x u
                 ; (m = i1) → compPathP-filler' {P = P} hq c o k })
        (h (compPath-filler p q (~ o) m)
           (compPathP-filler {P = S} sp sq (~ o) m))

-- Cubes in a groupoid: any two parallel squares with prescribed
-- matching sides are connected. This is the only truncation principle
-- used by the νGpd storey.
isGroupoid→Cube : {A : Set ℓ} (gA : isGroupoid A)
  {a₀₀ a₀₁ a₁₀ a₁₁ : I → A}
  {a₀₋ : (m : I) → a₀₀ m ≡ a₀₁ m} {a₁₋ : (m : I) → a₁₀ m ≡ a₁₁ m}
  {a₋₀ : (m : I) → a₀₀ m ≡ a₁₀ m} {a₋₁ : (m : I) → a₀₁ m ≡ a₁₁ m}
  (sq₀ : Square (a₀₋ i0) (a₁₋ i0) (a₋₀ i0) (a₋₁ i0))
  (sq₁ : Square (a₀₋ i1) (a₁₋ i1) (a₋₀ i1) (a₋₁ i1))
  → PathP (λ m → Square (a₀₋ m) (a₁₋ m) (a₋₀ m) (a₋₁ m)) sq₀ sq₁
isGroupoid→Cube {A = A} gA {a₀₋ = a₀₋} {a₁₋} {a₋₀} {a₋₁} sq₀ sq₁ =
  isProp→PathP
    (λ m → isSet→isPropPathP (λ i → a₋₀ m i ≡ a₋₁ m i)
             (gA (a₋₀ m i1) (a₋₁ m i1)) (a₀₋ m) (a₁₋ m))
    sq₀ sq₁

-- Transporting a dependent square along a groupoid-filled cube: given
-- the four lateral squares over the cube's given side faces — sharing
-- their corner edges by the shape of the telescope — the composition
-- over the isGroupoid→Cube interior carries a SquareP over the cube's
-- one end square to one over the other.
module _ {ℓ ℓ' : Level} {X : Set ℓ} {P : X → Set ℓ'} (gX : isGroupoid X)
  {a₀₀ a₀₁ a₁₀ a₁₁ : I → X}
  {a₀₋ : (m : I) → a₀₀ m ≡ a₀₁ m} {a₁₋ : (m : I) → a₁₀ m ≡ a₁₁ m}
  {a₋₀ : (m : I) → a₀₀ m ≡ a₁₀ m} {a₋₁ : (m : I) → a₀₁ m ≡ a₁₁ m}
  (sq₀ : Square (a₀₋ i0) (a₁₋ i0) (a₋₀ i0) (a₋₁ i0))
  (sq₁ : Square (a₀₋ i1) (a₁₋ i1) (a₋₀ i1) (a₋₁ i1))
  {v₀₀ : P (a₀₀ i0)} {v₀₁ : P (a₀₁ i0)}
  {v₁₀ : P (a₁₀ i0)} {v₁₁ : P (a₁₁ i0)}
  {V₀₀ : P (a₀₀ i1)} {V₀₁ : P (a₀₁ i1)}
  {V₁₀ : P (a₁₀ i1)} {V₁₁ : P (a₁₁ i1)}
  {g₀₀ : PathP (λ m → P (a₀₀ m)) v₀₀ V₀₀}
  {g₀₁ : PathP (λ m → P (a₀₁ m)) v₀₁ V₀₁}
  {g₁₀ : PathP (λ m → P (a₁₀ m)) v₁₀ V₁₀}
  {g₁₁ : PathP (λ m → P (a₁₁ m)) v₁₁ V₁₁}
  {f₀ : PathP (λ j → P (a₀₋ i0 j)) v₀₀ v₀₁}
  {f₁ : PathP (λ j → P (a₁₋ i0 j)) v₁₀ v₁₁}
  {fC : PathP (λ i → P (a₋₀ i0 i)) v₀₀ v₁₀}
  {fD : PathP (λ i → P (a₋₁ i0 i)) v₀₁ v₁₁}
  {F₀ : PathP (λ j → P (a₀₋ i1 j)) V₀₀ V₀₁}
  {F₁ : PathP (λ j → P (a₁₋ i1 j)) V₁₀ V₁₁}
  {FC : PathP (λ i → P (a₋₀ i1 i)) V₀₀ V₁₀}
  {FD : PathP (λ i → P (a₋₁ i1 i)) V₀₁ V₁₁}
  (L₀ : SquareP (λ m j → P (a₀₋ m j)) f₀ F₀ g₀₀ g₀₁)
  (L₁ : SquareP (λ m j → P (a₁₋ m j)) f₁ F₁ g₁₀ g₁₁)
  (LC : SquareP (λ m i → P (a₋₀ m i)) fC FC g₀₀ g₁₀)
  (LD : SquareP (λ m i → P (a₋₁ m i)) fD FD g₀₁ g₁₁)
  (σ : SquareP (λ i j → P (sq₀ i j)) f₀ f₁ fC fD)
  where

  squarePOverCube : SquareP (λ i j → P (sq₁ i j)) F₀ F₁ FC FD
  squarePOverCube i j =
    comp′ (λ m → P (isGroupoid→Cube gX {a₀₋ = a₀₋} {a₁₋ = a₁₋}
                      {a₋₀ = a₋₀} {a₋₁ = a₋₁} sq₀ sq₁ m i j))
      (λ m → λ { (i = i0) → L₀ m j
               ; (i = i1) → L₁ m j
               ; (j = i0) → LC m i
               ; (j = i1) → LD m i })
      (σ i j)

-- The filler of the layer-coherence square: the dependent square whose
-- i1 side is cohLayer-squareP's composition and whose other three
-- sides are that composition's base (the painting coherence) and side
-- fillers. The νGpd tower's s = 0 painting 2-coherence IS this
-- square, exactly as the νSet tower's r = 0 painting coherence is
-- subst-filler.
cohLayer-fillP :
  {ℓt ℓx ℓp ℓs : Level}
  {T1 : Set ℓt} {T2 T3 : Set ℓs} {X : Set ℓx} {P : X → Set ℓp}
  {S2 : T2 → Set ℓp} {S3 : T3 → Set ℓp}
  {rf0 : T1 → X} {rfF : T2 → X} {rfG : T3 → X}
  {F : (m : T2) → S2 m → P (rfF m)}
  {G : (n : T3) → S3 n → P (rfG n)}
  {d1 d2 : T1} {E1 : d1 ≡ d2}
  {m1 m2 : T2} {C2 : m1 ≡ m2}
  {n1 n2 : T3} {D2 : n1 ≡ n2}
  {C1 : rfF m2 ≡ rf0 d1}
  {D1 : rfG n2 ≡ rf0 d2}
  {K : rfF m1 ≡ rfG n1}
  {aL : S2 m1} {aR : S3 n1}
  (HCP : PathP (λ i → P (K i)) (F m1 aL) (G n1 aR))
  (sq : Square K (cong rf0 E1)
          (cong rfF C2 ∙ C1) (cong rfG D2 ∙ D1))
  → SquareP (λ j i → P (sq j i))
      HCP
      (cohLayer-squareP {P = P} {S2 = S2} {S3 = S3} {rf0 = rf0}
        {rfF = rfF} {rfG = rfG} {F = F} {G = G} {E1 = E1}
        {m1 = m1} {m2 = m2} {C2 = C2} {n1 = n1} {n2 = n2} {D2 = D2}
        {C1 = C1} {D1 = D1} {K = K} {aL = aL} {aR = aR} HCP sq)
      (compPathP {P = P}
        (λ j → F (C2 j) (subst-filler S2 C2 aL j))
        (subst-filler P C1 (F m2 (subst S2 C2 aL))))
      (compPathP {P = P}
        (λ j → G (D2 j) (subst-filler S3 D2 aR j))
        (subst-filler P D1 (G n2 (subst S3 D2 aR))))
cohLayer-fillP {P = P} {S2 = S2} {S3 = S3} {rf0 = rf0} {rfF = rfF}
  {rfG = rfG} {F = F} {G = G} {E1 = E1} {m1 = m1} {m2 = m2} {C2 = C2}
  {n1 = n1} {n2 = n2} {D2 = D2} {C1 = C1} {D1 = D1} {K = K}
  {aL = aL} {aR = aR} HCP sq j i =
  fill′ (λ j' → P (sq j' i))
        (λ j' → λ { (i = i0) → α j' ; (i = i1) → β j' })
        (inS (HCP i)) j
  where
  α : PathP (λ j → P ((cong rfF C2 ∙ C1) j))
        (F m1 aL) (subst P C1 (F m2 (subst S2 C2 aL)))
  α = compPathP {P = P}
        (λ j → F (C2 j) (subst-filler S2 C2 aL j))
        (subst-filler P C1 (F m2 (subst S2 C2 aL)))
  β : PathP (λ j → P ((cong rfG D2 ∙ D1) j))
        (G n1 aR) (subst P D1 (G n2 (subst S3 D2 aR)))
  β = compPathP {P = P}
        (λ j → G (D2 j) (subst-filler S3 D2 aR j))
        (subst-filler P D1 (G n2 (subst S3 D2 aR)))

------------------------------------------------------------------------
-- The fused assembly lemma for the layer 2-coherence, stated over
-- abstract families.
--
-- The layer 2-coherence's proof pastes conjugation squares, canonical
-- fillers and junction cells into the four lateral faces of a cube and
-- transports the painting 2-coherence across its isGroupoid interior.
-- Checked at the tower's types, every Kan operation in the mid-level
-- fibers computes componentwise (the fibers are literal Σ/Π types
-- there), so each face-compatibility check of the pasting
-- re-normalizes component trees with no sharing. Stated over abstract
-- families, the same fillers are neutral: the pasting is checked once,
-- structurally, here; a use site checks leaf arguments against the
-- instantiated parameter types and its boundary against the stated
-- faces.
--
-- The parameters are one storey of tower data. X, Y, Z are the frame
-- domains of three consecutive dimensions with painting families P, S,
-- T̃; R restricts Y to X along an arity point t (w below); rfq/rfr/rfs
-- with Fq/Fr/Fs are the q-, r- and s-face restrictions and paintings
-- one storey down, w⁺/r̂fr/r̂fs/r̂fsq/r̂fsr/r̂ss the corresponding maps one
-- storey up. The κ-families are the arity-point conjugators (the
-- q/r/s-face coherences against the 0-face), the K/H-families the
-- face-commutation coherences and painting coherences between two
-- faces. The six fillers enter as opaque dependent squares typed by
-- cohLayer-fillP's stated output; all junction seams below are between
-- stated faces. The exposed lemma is coh2Layer-cubeP, the closing
-- form at the goal base: the pasting over the padded base (the private
-- cube) carried back across the base pad along the given side cells.
--
-- The telescope is staged across three nested anonymous modules: the
-- data through the six base squares first, then the four fillers the
-- laterals consume, then fillC/fillD and the premises. Anonymous
-- nesting leaves the lifted parameter order of coh2Layer-cubeP
-- unchanged. Every definition in a section is processed over its whole
-- telescope, so each private binding lives in the innermost module whose
-- parameters it mentions and avoids the later, large filler and premise
-- types.
------------------------------------------------------------------------
module _
  {ℓx ℓy ℓz ℓa ℓp : Level}
  {X : Set ℓx} {P : X → Set ℓp}
  {Y : Set ℓy} {S : Y → Set ℓp}
  {Z : Set ℓz} {T̃ : Z → Set ℓp}
  {T : Set ℓa}
  (gX : isGroupoid X)
  (R : Y → T → X) (t : T)
  -- Y-to-X restrictions and paintings
  (rfq rfr rfs : Y → X)
  (Fq : (y : Y) → S y → P (rfq y))
  (Fr : (y : Y) → S y → P (rfr y))
  (Fs : (y : Y) → S y → P (rfs y))
  -- Z-to-Y restrictions and paintings
  (w⁺ r̂fr r̂fs r̂fsq r̂fsr r̂ss : Z → Y)
  (F̂r  : (z : Z) → T̃ z → S (r̂fr z))
  (Ĝs  : (z : Z) → T̃ z → S (r̂fs z))
  (F̂sq : (z : Z) → T̃ z → S (r̂fsq z))
  (F̂sr : (z : Z) → T̃ z → S (r̂fsr z))
  -- arity-point conjugator families
  (κqf : (z : Z) → rfq (w⁺ z) ≡ R (r̂fsq z) t)
  (κrf : (z : Z) → rfr (w⁺ z) ≡ R (r̂fsr z) t)
  (κsf : (z : Z) → rfs (w⁺ z) ≡ R (r̂ss z) t)
  -- face-commutation and painting-coherence families
  (Kqr : (z : Z) → rfq (r̂fr z) ≡ rfr (r̂fsq z))
  (Hqr : (z : Z) (c : T̃ z)
         → PathP (λ i → P (Kqr z i)) (Fq (r̂fr z) (F̂r z c))
             (Fr (r̂fsq z) (F̂sq z c)))
  (Kqs : (z : Z) → rfq (r̂fs z) ≡ rfs (r̂fsq z))
  (Hqs : (z : Z) (c : T̃ z)
         → PathP (λ i → P (Kqs z i)) (Fq (r̂fs z) (Ĝs z c))
             (Fs (r̂fsq z) (F̂sq z c)))
  (Krs : (z : Z) → rfr (r̂fs z) ≡ rfs (r̂fsr z))
  (Hrs : (z : Z) (c : T̃ z)
         → PathP (λ i → P (Krs z i)) (Fr (r̂fs z) (Ĝs z c))
             (Fs (r̂fsr z) (F̂sr z c)))
  -- the Z-level points, conjugators and transported elements
  {mSb bK nRb bC nEb bD : Z}
  {dRK dEK dRC dRD dEC dED : Z}
  (κ'  : mSb ≡ bK) (cS̃ : T̃ mSb)
  (κ'C : nRb ≡ bC) (c̃C : T̃ nRb)
  (κ'E : nEb ≡ bD) (c̃E : T̃ nEb)
  -- the Z- and Y-level paths of the six filler packs
  (C2f' : dRK ≡ dRC) (D2f' : dEK ≡ dRD) (E1f : dEC ≡ dED)
  (C2K : r̂fr bK ≡ w⁺ dRK) (D2K : r̂fsq bK ≡ w⁺ dEK)
  (sC : r̂fs bC ≡ w⁺ dRC) (sD : r̂fs bD ≡ w⁺ dRD)
  (D2C : r̂fsq bC ≡ w⁺ dEC) (D1E1 : r̂fsr bD ≡ w⁺ dED)
  (KC2 : r̂fr mSb ≡ r̂fs nRb) (KD2 : r̂fsq mSb ≡ r̂fs nEb)
  (KE1 : r̂fsq nRb ≡ r̂fsr nEb)
  (E1K : r̂fsq dRK ≡ r̂fsr dEK)
  (qCb : r̂fsq dRC ≡ r̂ss dEC) (qDb : r̂fsr dRD ≡ r̂ss dED)
  -- the mid-level painting-coherence premises of the upper fillers
  (HCPC2 : PathP (λ i → S (KC2 i)) (F̂r mSb cS̃) (Ĝs nRb c̃C))
  (HCPD2 : PathP (λ i → S (KD2 i)) (F̂sq mSb cS̃) (Ĝs nEb c̃E))
  (HCPE1 : PathP (λ i → S (KE1 i)) (F̂sq nRb c̃C) (F̂sr nEb c̃E))
  -- the six base squares
  (sqK : Square (Kqr bK) (cong (λ y → R y t) E1K)
           (cong rfq C2K ∙ κqf dRK) (cong rfr D2K ∙ κrf dEK))
  (sqE1 : Square KE1 (cong w⁺ E1f)
            (cong r̂fsq κ'C ∙ D2C) (cong r̂fsr κ'E ∙ D1E1))
  (sqC2' : Square KC2 (cong w⁺ C2f')
             (cong r̂fr κ' ∙ C2K) (cong r̂fs κ'C ∙ sC))
  (sqD2' : Square KD2 (cong w⁺ D2f')
             (cong r̂fsq κ' ∙ D2K) (cong r̂fs κ'E ∙ sD))
  (sqC : Square (Kqs bC) (cong (λ y → R y t) qCb)
           (cong rfq sC ∙ κqf dRC) (cong rfs D2C ∙ κsf dEC))
  (sqD : Square (Krs bD) (cong (λ y → R y t) qDb)
           (cong rfr sD ∙ κrf dRD) (cong rfs D1E1 ∙ κsf dED))
  where
  private

    w : Y → X
    w y = R y t

    -- transported slice elements
    aSK = subst T̃ κ' cS̃
    ŝf  = subst-filler T̃ κ' cS̃
    ŝfC = subst-filler T̃ κ'C c̃C
    ŝfE = subst-filler T̃ κ'E c̃E
    lRC = subst T̃ κ'C c̃C
    lED = subst T̃ κ'E c̃E
    aLK = F̂r bK aSK
    aRK = F̂sq bK aSK
    XC  = Ĝs bC lRC
    aRC = F̂sq bC lRC
    XD  = Ĝs bD lED
    aRD = F̂sr bD lED
    jbK = junctionP.base {P = P} rfq (cong r̂fr κ') C2K (κqf dRK)
    jbMC = junctionP.base {P = P} rfq (cong r̂fs κ'C) sC (κqf dRC)
    jbE = junctionP.base {P = P} rfs (cong r̂fsq κ'C) D2C (κsf dEC)
    jb0D = junctionP.base {P = P} rfr (cong r̂fsq κ') D2K (κrf dEK)
    jbMD = junctionP.base {P = P} rfr (cong r̂fs κ'E) sD (κrf dRD)
    jb1D = junctionP.base {P = P} rfs (cong r̂fsr κ'E) D1E1 (κsf dED)
    κE1 : (jj : I) → rfs (w⁺ (E1f jj)) ≡ R (r̂ss (E1f jj)) t
    κE1 = λ jj → κsf (E1f jj)
    κC : (ii : I) → rfq (w⁺ (C2f' ii)) ≡ R (r̂fsq (C2f' ii)) t
    κC = λ ii → κqf (C2f' ii)
    κD : (ii : I) → rfr (w⁺ (D2f' ii)) ≡ R (r̂fsr (D2f' ii)) t
    κD = λ ii → κrf (D2f' ii)
    -- the lateral base squares, named so the cube's face families are
    -- single definitions
    L₀b = ∙v (λ m jj → Kqr (κ' m) jj) sqK
    L₁b = ∙v (λ m jj → rfs (sqE1 m jj)) (λ m jj → κE1 jj m)
    σub = ∙v (λ m ii → rfq (sqC2' m ii)) (λ m ii → κC ii m)
    σvb = ∙v (λ m ii → Kqs (κ'C m) ii) sqC
    σu'b = pad σub (λ o m → σub m i0) jbMC
    LCb = pad (∙slice σu'b σvb) jbK (λ o m → jbE (~ o) m)
    σdb = ∙v (λ m ii → rfr (sqD2' m ii)) (λ m ii → κD ii m)
    σeb = ∙v (λ m ii → Krs (κ'E m) ii) sqD
    σd'b = pad σdb (λ o m → σdb m i0) jbMD
    LDb = pad (∙slice σd'b σeb) jb0D (λ o m → jb1D (~ o) m)

  module _
    -- the six fillers, at cohLayer-fillP's stated output types
    (fillK : SquareP (λ j i → P (sqK j i))
        (Hqr bK (subst T̃ κ' cS̃))
        (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = λ y → R y t}
          {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr} {E1 = E1K}
          {C2 = C2K} {D2 = D2K} {C1 = κqf dRK} {D1 = κrf dEK}
          {K = Kqr bK} {aL = F̂r bK (subst T̃ κ' cS̃)} {aR = F̂sq bK (subst T̃ κ' cS̃)}
          (Hqr bK (subst T̃ κ' cS̃)) sqK)
        (compPathP {P = P}
          (λ j → Fq (C2K j) (subst-filler S C2K (F̂r bK (subst T̃ κ' cS̃)) j))
          (subst-filler P (κqf dRK) (Fq (w⁺ dRK) (subst S C2K (F̂r bK (subst T̃ κ' cS̃))))))
        (compPathP {P = P}
          (λ j → Fr (D2K j) (subst-filler S D2K (F̂sq bK (subst T̃ κ' cS̃)) j))
          (subst-filler P (κrf dEK) (Fr (w⁺ dEK) (subst S D2K (F̂sq bK (subst T̃ κ' cS̃)))))))
    (fillPE1 : SquareP (λ j i → S (sqE1 j i))
        HCPE1
        (cohLayer-squareP {P = S} {S2 = T̃} {S3 = T̃} {rf0 = w⁺}
          {rfF = r̂fsq} {rfG = r̂fsr} {F = F̂sq} {G = F̂sr} {E1 = E1f}
          {C2 = κ'C} {D2 = κ'E} {C1 = D2C} {D1 = D1E1}
          {K = KE1} {aL = c̃C} {aR = c̃E}
          HCPE1 sqE1)
        (compPathP {P = S}
          (λ j → F̂sq (κ'C j) (subst-filler T̃ κ'C c̃C j))
          (subst-filler S D2C (F̂sq bC (subst T̃ κ'C c̃C))))
        (compPathP {P = S}
          (λ j → F̂sr (κ'E j) (subst-filler T̃ κ'E c̃E j))
          (subst-filler S D1E1 (F̂sr bD (subst T̃ κ'E c̃E)))))
    (fillC2 : SquareP (λ j i → S (sqC2' j i))
        HCPC2
        (cohLayer-squareP {P = S} {S2 = T̃} {S3 = T̃} {rf0 = w⁺}
          {rfF = r̂fr} {rfG = r̂fs} {F = F̂r} {G = Ĝs} {E1 = C2f'}
          {C2 = κ'} {D2 = κ'C} {C1 = C2K} {D1 = sC}
          {K = KC2} {aL = cS̃} {aR = c̃C}
          HCPC2 sqC2')
        (compPathP {P = S}
          (λ j → F̂r (κ' j) (subst-filler T̃ κ' cS̃ j))
          (subst-filler S C2K (F̂r bK (subst T̃ κ' cS̃))))
        (compPathP {P = S}
          (λ j → Ĝs (κ'C j) (subst-filler T̃ κ'C c̃C j))
          (subst-filler S sC (Ĝs bC (subst T̃ κ'C c̃C)))))
    (fillD2 : SquareP (λ j i → S (sqD2' j i))
        HCPD2
        (cohLayer-squareP {P = S} {S2 = T̃} {S3 = T̃} {rf0 = w⁺}
          {rfF = r̂fsq} {rfG = r̂fs} {F = F̂sq} {G = Ĝs} {E1 = D2f'}
          {C2 = κ'} {D2 = κ'E} {C1 = D2K} {D1 = sD}
          {K = KD2} {aL = cS̃} {aR = c̃E}
          HCPD2 sqD2')
        (compPathP {P = S}
          (λ j → F̂sq (κ' j) (subst-filler T̃ κ' cS̃ j))
          (subst-filler S D2K (F̂sq bK (subst T̃ κ' cS̃))))
        (compPathP {P = S}
          (λ j → Ĝs (κ'E j) (subst-filler T̃ κ'E c̃E j))
          (subst-filler S sD (Ĝs bD (subst T̃ κ'E c̃E)))))
    where
    private

      aE1 : (jj : I) → P (rfs (w⁺ (E1f jj)))
      aE1 = λ jj → Fs (w⁺ (E1f jj)) (fillPE1 i1 jj)
      aC : (ii : I) → P (rfq (w⁺ (C2f' ii)))
      aC = λ ii → Fq (w⁺ (C2f' ii)) (fillC2 i1 ii)
      aD : (ii : I) → P (rfr (w⁺ (D2f' ii)))
      aD = λ ii → Fr (w⁺ (D2f' ii)) (fillD2 i1 ii)

      -- the i = i0 lateral: the K-side conjugation composed with fillK
      L₀ : SquareP (λ m jj → P (L₀b m jj))
        (Hqr mSb cS̃)
        (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = w}
          {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr} {E1 = E1K}
          {C2 = C2K} {D2 = D2K} {C1 = κqf dRK} {D1 = κrf dEK}
          {K = Kqr bK} {aL = aLK} {aR = aRK}
          (Hqr bK aSK) sqK)
        (compPathP {P = P} (λ m → Hqr (κ' m) (ŝf m) i0)
           (λ m → fillK m i0))
        (compPathP {P = P} (λ m → Hqr (κ' m) (ŝf m) i1)
           (λ m → fillK m i1))
      L₀ = ∙vP {P = P}
        {B₁ = λ m jj → Kqr (κ' m) jj}
        {B₂ = sqK}
        (λ m jj → Hqr (κ' m) (ŝf m) jj)
        fillK

      -- the i = i1 lateral: the s-side application of fillPE1 composed
      -- with the arity-point transport
      L₁ : SquareP (λ m jj → P (L₁b m jj))
        (λ jj → Fs (KE1 jj) (HCPE1 jj))
        (λ jj → subst P (κE1 jj) (aE1 jj))
        (compPathP {P = P} (λ m → Fs (sqE1 m i0) (fillPE1 m i0))
           (λ m → subst-filler P (κE1 i0) (aE1 i0) m))
        (compPathP {P = P} (λ m → Fs (sqE1 m i1) (fillPE1 m i1))
           (λ m → subst-filler P (κE1 i1) (aE1 i1) m))
      L₁ = ∙vP {P = P}
        {B₁ = λ m jj → rfs (sqE1 m jj)}
        {B₂ = λ m jj → κE1 jj m}
        (λ m jj → Fs (sqE1 m jj) (fillPE1 m jj))
        (λ m jj → subst-filler P (κE1 jj) (aE1 jj) m)

      -- the j = i0 lateral (the C face)
      σu = ∙vP {P = P}
        {B₁ = λ m ii → rfq (sqC2' m ii)}
        {B₂ = λ m ii → κC ii m}
        (λ m ii → Fq (sqC2' m ii) (fillC2 m ii))
        (λ m ii → subst-filler P (κC ii) (aC ii) m)
      ccK = junctionP.cell {P = P} rfq (cong r̂fr κ') C2K (κqf dRK) Fq
        (λ m → F̂r (κ' m) (ŝf m)) (subst-filler S C2K aLK)
        (subst-filler P (κqf dRK) (aC i0))
      ccMC = junctionP.cell {P = P} rfq (cong r̂fs κ'C) sC (κqf dRC) Fq
        (λ m → Ĝs (κ'C m) (ŝfC m)) (subst-filler S sC XC)
        (subst-filler P (κqf dRC) (aC i1))
      ccE = junctionP.cell {P = P} rfs (cong r̂fsq κ'C) D2C (κsf dEC) Fs
        (λ m → F̂sq (κ'C m) (ŝfC m)) (subst-filler S D2C aRC)
        (subst-filler P (κsf dEC) (aE1 i0))
      σu' = padP {P = P} σu (λ o m → σu m i0) ccMC
      -- the j = i1 lateral (the D face)
      σd = ∙vP {P = P}
        {B₁ = λ m ii → rfr (sqD2' m ii)}
        {B₂ = λ m ii → κD ii m}
        (λ m ii → Fr (sqD2' m ii) (fillD2 m ii))
        (λ m ii → subst-filler P (κD ii) (aD ii) m)
      cc0D = junctionP.cell {P = P} rfr (cong r̂fsq κ') D2K (κrf dEK) Fr
        (λ m → F̂sq (κ' m) (ŝf m)) (subst-filler S D2K aRK)
        (subst-filler P (κrf dEK) (aD i0))
      ccMD = junctionP.cell {P = P} rfr (cong r̂fs κ'E) sD (κrf dRD) Fr
        (λ m → Ĝs (κ'E m) (ŝfE m)) (subst-filler S sD XD)
        (subst-filler P (κrf dRD) (aD i1))
      cc1D = junctionP.cell {P = P} rfs (cong r̂fsr κ'E) D1E1 (κsf dED) Fs
        (λ m → F̂sr (κ'E m) (ŝfE m)) (subst-filler S D1E1 aRD)
        (subst-filler P (κsf dED) (aE1 i1))
      σd' = padP {P = P} σd (λ o m → σd m i0) ccMD

      -- the cube's corner edges, named and stated
      g00 : PathP (λ m → P (L₀b m i0))
          (Fq (r̂fr mSb) (F̂r mSb cS̃))
          (subst P (κqf dRK) (Fq (w⁺ dRK) (subst S C2K aLK)))
      g00 = compPathP {P = P} (λ m → Hqr (κ' m) (ŝf m) i0)
              (λ m → fillK m i0)
      g01 : PathP (λ m → P (L₀b m i1))
          (Fr (r̂fsq mSb) (F̂sq mSb cS̃))
          (subst P (κrf dEK) (Fr (w⁺ dEK) (subst S D2K aRK)))
      g01 = compPathP {P = P} (λ m → Hqr (κ' m) (ŝf m) i1)
              (λ m → fillK m i1)
      g10 : PathP (λ m → P (L₁b m i0))
          (Fs (r̂fsq nRb) (F̂sq nRb c̃C))
          (subst P (κE1 i0) (aE1 i0))
      g10 = compPathP {P = P} (λ m → Fs (sqE1 m i0) (fillPE1 m i0))
              (λ m → subst-filler P (κE1 i0) (aE1 i0) m)
      g11 : PathP (λ m → P (L₁b m i1))
          (Fs (r̂fsr nEb) (F̂sr nEb c̃E))
          (subst P (κE1 i1) (aE1 i1))
      g11 = compPathP {P = P} (λ m → Fs (sqE1 m i1) (fillPE1 m i1))
              (λ m → subst-filler P (κE1 i1) (aE1 i1) m)

      -- the cube's stated output faces, named
      F0c = cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = w}
            {rfF = rfq} {rfG = rfr} {F = Fq} {G = Fr} {E1 = E1K}
            {C2 = C2K} {D2 = D2K} {C1 = κqf dRK} {D1 = κrf dEK}
            {K = Kqr bK} {aL = aLK} {aR = aRK}
            (Hqr bK aSK) sqK
      F1c : PathP (λ jj → P (R (r̂ss (E1f jj)) t))
          (subst P (κE1 i0) (aE1 i0)) (subst P (κE1 i1) (aE1 i1))
      F1c = λ jj → subst P (κE1 jj) (aE1 jj)
      FCc : PathP (λ ii → P (((λ i' → R (r̂fsq (C2f' i')) t)
                              ∙ (λ i' → R (qCb i') t)) ii))
          (subst P (κqf dRK) (aC i0))
          (subst P (κsf dEC) (Fs (w⁺ dEC) (subst S D2C aRC)))
      FCc = compPathP {P = P} (λ ii → subst P (κC ii) (aC ii))
            (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = w}
              {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs} {E1 = qCb}
              {C2 = sC} {D2 = D2C} {C1 = κqf dRC} {D1 = κsf dEC}
              {K = Kqs bC} {aL = XC} {aR = aRC}
              (Hqs bC lRC) sqC)
      FDc : PathP (λ ii → P (((λ i' → R (r̂fsr (D2f' i')) t)
                              ∙ (λ i' → R (qDb i') t)) ii))
          (subst P (κrf dEK) (aD i0))
          (subst P (κsf dED) (Fs (w⁺ dED) (subst S D1E1 aRD)))
      FDc = compPathP {P = P} (λ ii → subst P (κD ii) (aD ii))
            (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = w}
              {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs} {E1 = qDb}
              {C2 = sD} {D2 = D1E1} {C1 = κrf dRD} {D1 = κsf dED}
              {K = Krs bD} {aL = XD} {aR = aRD}
              (Hrs bD lED) sqD)

    module _
      (fillC : SquareP (λ j i → P (sqC j i))
          (Hqs bC (subst T̃ κ'C c̃C))
          (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = λ y → R y t}
            {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs} {E1 = qCb}
            {C2 = sC} {D2 = D2C} {C1 = κqf dRC} {D1 = κsf dEC}
            {K = Kqs bC} {aL = Ĝs bC (subst T̃ κ'C c̃C)}
            {aR = F̂sq bC (subst T̃ κ'C c̃C)}
            (Hqs bC (subst T̃ κ'C c̃C)) sqC)
          (compPathP {P = P}
            (λ j → Fq (sC j) (subst-filler S sC (Ĝs bC (subst T̃ κ'C c̃C)) j))
            (subst-filler P (κqf dRC)
              (Fq (w⁺ dRC) (subst S sC (Ĝs bC (subst T̃ κ'C c̃C))))))
          (compPathP {P = P}
            (λ j → Fs (D2C j) (subst-filler S D2C (F̂sq bC (subst T̃ κ'C c̃C)) j))
            (subst-filler P (κsf dEC)
              (Fs (w⁺ dEC) (subst S D2C (F̂sq bC (subst T̃ κ'C c̃C)))))))
      (fillD : SquareP (λ j i → P (sqD j i))
          (Hrs bD (subst T̃ κ'E c̃E))
          (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = λ y → R y t}
            {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs} {E1 = qDb}
            {C2 = sD} {D2 = D1E1} {C1 = κrf dRD} {D1 = κsf dED}
            {K = Krs bD} {aL = Ĝs bD (subst T̃ κ'E c̃E)}
            {aR = F̂sr bD (subst T̃ κ'E c̃E)}
            (Hrs bD (subst T̃ κ'E c̃E)) sqD)
          (compPathP {P = P}
            (λ j → Fr (sD j) (subst-filler S sD (Ĝs bD (subst T̃ κ'E c̃E)) j))
            (subst-filler P (κrf dRD)
              (Fr (w⁺ dRD) (subst S sD (Ĝs bD (subst T̃ κ'E c̃E))))))
          (compPathP {P = P}
            (λ j → Fs (D1E1 j) (subst-filler S D1E1 (F̂sr bD (subst T̃ κ'E c̃E)) j))
            (subst-filler P (κsf dED)
              (Fs (w⁺ dED) (subst S D1E1 (F̂sr bD (subst T̃ κ'E c̃E)))))))
      -- the premise: the painting 2-coherence at the arity-point-restricted
      -- point, with the faces spelled as the laterals' premise-side faces
      (B₀ : Square (Kqr mSb) (cong rfs KE1)
              (cong rfq KC2 ∙ Kqs nRb) (cong rfr KD2 ∙ Krs nEb))
      (σp : SquareP (λ i j → P (B₀ i j))
              (Hqr mSb cS̃)
              (λ jj → Fs (KE1 jj) (HCPE1 jj))
              (compPathP {P = P} (λ ii → Fq (KC2 ii) (HCPC2 ii)) (Hqs nRb c̃C))
              (compPathP {P = P} (λ ii → Fr (KD2 ii) (HCPD2 ii)) (Hrs nEb c̃E)))
      -- the goal base square and the base cells padding its side edges
      -- from the applied composites to the laterals' pointwise composites
      (BG : Square (cong (λ y → R y t) E1K)
              (λ jj → R (r̂ss (E1f jj)) t)
              (λ ii → R ((cong r̂fsq C2f' ∙ qCb) ii) t)
              (λ ii → R ((cong r̂fsr D2f' ∙ qDb) ii) t))
      (BCL : Square (λ ii → R ((cong r̂fsq C2f' ∙ qCb) ii) t)
               ((λ ii → R (r̂fsq (C2f' ii)) t) ∙ (λ ii → R (qCb ii) t))
               (λ _ → R (r̂fsq dRK) t) (λ _ → R (r̂ss dEC) t))
      (BCR : Square (λ ii → R ((cong r̂fsr D2f' ∙ qDb) ii) t)
               ((λ ii → R (r̂fsr (D2f' ii)) t) ∙ (λ ii → R (qDb ii) t))
               (λ _ → R (r̂fsr dEK) t) (λ _ → R (r̂ss dED) t))
      where
      private

        -- the cube's far base square: the goal base padded to the laterals'
        -- m = i1 base edges
        sq₁b : Square (cong (λ y → R y t) E1K)
            (λ jj → R (r̂ss (E1f jj)) t)
            ((λ ii → R (r̂fsq (C2f' ii)) t) ∙ (λ ii → R (qCb ii) t))
            ((λ ii → R (r̂fsr (D2f' ii)) t) ∙ (λ ii → R (qDb ii) t))
        sq₁b = pad {X = X} BG BCL BCR
        σv = ∙vP {P = P}
          {B₁ = λ m ii → Kqs (κ'C m) ii}
          {B₂ = sqC}
          (λ m ii → Hqs (κ'C m) (ŝfC m) ii)
          fillC
        σe = ∙vP {P = P}
          {B₁ = λ m ii → Krs (κ'E m) ii}
          {B₂ = sqD}
          (λ m ii → Hrs (κ'E m) (ŝfE m) ii)
          fillD
        LC : SquareP (λ m ii → P (LCb m ii))
          (compPathP {P = P} (λ ii → Fq (KC2 ii) (HCPC2 ii)) (Hqs nRb c̃C))
          (compPathP {P = P} (λ ii → subst P (κC ii) (aC ii))
            (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = w}
              {rfF = rfq} {rfG = rfs} {F = Fq} {G = Fs} {E1 = qCb}
              {C2 = sC} {D2 = D2C} {C1 = κqf dRC} {D1 = κsf dEC}
              {K = Kqs bC} {aL = XC} {aR = aRC}
              (Hqs bC lRC) sqC))
          (compPathP {P = P} (λ m → Hqr (κ' m) (ŝf m) i0)
             (λ m → fillK m i0))
          (compPathP {P = P} (λ m → Fs (sqE1 m i0) (fillPE1 m i0))
             (λ m → subst-filler P (κE1 i0) (aE1 i0) m))
        LC = padP {P = P} (∙sliceP {P = P} σu' σv) ccK (λ o m → ccE (~ o) m)
        LD : SquareP (λ m ii → P (LDb m ii))
          (compPathP {P = P} (λ ii → Fr (KD2 ii) (HCPD2 ii)) (Hrs nEb c̃E))
          (compPathP {P = P} (λ ii → subst P (κD ii) (aD ii))
            (cohLayer-squareP {P = P} {S2 = S} {S3 = S} {rf0 = w}
              {rfF = rfr} {rfG = rfs} {F = Fr} {G = Fs} {E1 = qDb}
              {C2 = sD} {D2 = D1E1} {C1 = κrf dRD} {D1 = κsf dED}
              {K = Krs bD} {aL = XD} {aR = aRD}
              (Hrs bD lED) sqD))
          (compPathP {P = P} (λ m → Hqr (κ' m) (ŝf m) i1) (λ m → fillK m i1))
          (compPathP {P = P} (λ m → Fs (sqE1 m i1) (fillPE1 m i1))
             (λ m → subst-filler P (κE1 i1) (aE1 i1) m))
        LD = padP {P = P} (∙sliceP {P = P} σd' σe) cc0D (λ o m → cc1D (~ o) m)

        -- the cube: the painting 2-coherence premise transported across the
        -- isGroupoid interior along the four laterals
        cube = squarePOverCube {X = X} {P = P} gX
          {a₀₀ = λ m → L₀b m i0} {a₀₁ = λ m → L₀b m i1}
          {a₁₀ = λ m → L₁b m i0} {a₁₁ = λ m → L₁b m i1}
          {a₀₋ = λ m → L₀b m} {a₁₋ = λ m → L₁b m}
          {a₋₀ = λ m → LCb m} {a₋₁ = λ m → LDb m}
          B₀ sq₁b
          {v₀₀ = Fq (r̂fr mSb) (F̂r mSb cS̃)}
          {v₀₁ = Fr (r̂fsq mSb) (F̂sq mSb cS̃)}
          {v₁₀ = Fs (r̂fsq nRb) (F̂sq nRb c̃C)}
          {v₁₁ = Fs (r̂fsr nEb) (F̂sr nEb c̃E)}
          {V₀₀ = subst P (κqf dRK) (Fq (w⁺ dRK) (subst S C2K aLK))}
          {V₀₁ = subst P (κrf dEK) (Fr (w⁺ dEK) (subst S D2K aRK))}
          {V₁₀ = subst P (κE1 i0) (aE1 i0)}
          {V₁₁ = subst P (κE1 i1) (aE1 i1)}
          {g₀₀ = g00} {g₀₁ = g01} {g₁₀ = g10} {g₁₁ = g11}
          {f₀ = Hqr mSb cS̃}
          {f₁ = λ jj → Fs (KE1 jj) (HCPE1 jj)}
          {fC = compPathP {P = P} (λ ii → Fq (KC2 ii) (HCPC2 ii))
                  (Hqs nRb c̃C)}
          {fD = compPathP {P = P} (λ ii → Fr (KD2 ii) (HCPD2 ii))
                  (Hrs nEb c̃E)}
          {F₀ = F0c} {F₁ = F1c} {FC = FCc} {FD = FDc}
          L₀ L₁ LC LD σp

      -- the closing lemma: the cube carried back across the base pad, its
      -- side faces bridged by the given cells. The layer 2-coherence's
      -- clause is one application of coh2Layer-cubeP, as the layer coherence's is
      -- one of cohLayer-squareP.
      coh2Layer-cubeP :
        {gC : PathP (λ ii → P (R ((cong r̂fsq C2f' ∙ qCb) ii) t))
            (subst P (κqf dRK) (aC i0))
            (subst P (κsf dEC) (Fs (w⁺ dEC) (subst S D2C aRC)))}
        {gD : PathP (λ ii → P (R ((cong r̂fsr D2f' ∙ qDb) ii) t))
            (subst P (κrf dEK) (aD i0))
            (subst P (κsf dED) (Fs (w⁺ dED) (subst S D1E1 aRD)))}
        (CL : SquareP (λ o ii → P (BCL o ii)) gC FCc
            (λ _ → subst P (κqf dRK) (aC i0))
            (λ _ → subst P (κsf dEC) (Fs (w⁺ dEC) (subst S D2C aRC))))
        (CR : SquareP (λ o ii → P (BCR o ii)) gD FDc
            (λ _ → subst P (κrf dEK) (aD i0))
            (λ _ → subst P (κsf dED) (Fs (w⁺ dED) (subst S D1E1 aRD))))
        → SquareP (λ i j → P (BG i j)) F0c F1c gC gD
      coh2Layer-cubeP {gC} {gD} CL CR i j =
        comp′ (λ m → P (pad-fill BG BCL BCR (~ m) i j))
          (λ m → λ { (i = i0) → F0c j
                   ; (i = i1) → F1c j
                   ; (j = i0) → CL (~ m) i
                   ; (j = i1) → CR (~ m) i })
          (cube i j)
