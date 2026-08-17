------------------------------------------------------------------------
-- Bonak.RewLemmas — the PathP kit for the tower's coherences.
--
-- Bonak.νSet states its coherences as dependent paths over the frame
-- coherence, so the whole kit is: the transport filler, dependent-path
-- composition, and square filling in an HSet, combined into the one
-- layer-coherence lemma cohLayer-squareP.
------------------------------------------------------------------------

module Bonak.RewLemmas where

open import Bonak.Prelude

private variable
  ℓ ℓ' ℓ'' : Level
  A B : Set ℓ

-- The filler connecting x to its transport.
subst-filler : (P : A → Set ℓ') {x y : A} (p : x ≡ y) (u : P x)
               → PathP (λ i → P (p i)) u (subst P p u)
subst-filler P p u i =
  transp (λ j → P (p (i ∧ j))) (~ i) u

compPath-filler : {x y z : A} (p : x ≡ y) (q : y ≡ z)
                  → PathP (λ j → x ≡ q j) p (p ∙ q)
compPath-filler {x = x} p q j i =
  hfill (λ k → λ { (i = i0) → x ; (i = i1) → q k }) (inS (p i)) j

-- Composition of dependent paths over composition of base paths.
compPathP : {P : A → Set ℓ'} {x y z : A} {p : x ≡ y} {q : y ≡ z}
            {u : P x} {v : P y} {w : P z}
            → PathP (λ i → P (p i)) u v → PathP (λ i → P (q i)) v w
            → PathP (λ i → P ((p ∙ q) i)) u w
compPathP {P = P} {p = p} {q = q} {u = u} α β i =
  comp′ (λ j → P (compPath-filler p q j i))
        (λ j → λ { (i = i0) → u ; (i = i1) → β j })
        (α i)

-- Any four suitably-parallel paths in an HSet bound a square.
Square : {a₀₀ a₀₁ a₁₀ a₁₁ : A}
         (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
         (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁) → Set _
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

isSet→Square : isSet A → {a₀₀ a₀₁ a₁₀ a₁₁ : A}
               (a₀₋ : a₀₀ ≡ a₀₁) (a₁₋ : a₁₀ ≡ a₁₁)
               (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
               → Square a₀₋ a₁₋ a₋₀ a₋₁
isSet→Square sA a₀₋ a₁₋ a₋₀ a₋₁ =
  isProp→PathP (λ i → sA (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

-- The layer-coherence square: connect the two restr-layer transport
-- chains by a dependent path along E1, given the painting coherence as
-- a PathP over K and the 2-dimensional frame coherence as a Square
-- (free in an HSet of frames).

cohLayer-squareP :
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
  → PathP (λ i → P (K i)) (F m1 aL) (G n1 aR)
  → Square K (cong rf0 E1)
      (cong rfF C2 ∙ C1) (cong rfG D2 ∙ D1)
  → PathP (λ i → P (rf0 (E1 i)))
      (subst P C1 (F m2 (subst S2 C2 aL)))
      (subst P D1 (G n2 (subst S3 D2 aR)))
cohLayer-squareP {P = P} {S2 = S2} {S3 = S3} {rf0 = rf0} {rfF = rfF}
  {rfG = rfG} {F = F} {G = G} {E1 = E1} {m1 = m1} {m2 = m2} {C2 = C2}
  {n1 = n1} {n2 = n2} {D2 = D2} {C1 = C1} {D1 = D1} {K = K}
  {aL = aL} {aR = aR} HCP sq i =
  comp′ (λ j → P (sq j i))
        (λ j → λ { (i = i0) → α j ; (i = i1) → β j })
        (HCP i)
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
