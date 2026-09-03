import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isPullback_fibre_prod_and_slices_of_section
    {S K : Type u} [CommRing S] [CommRing K] (r : S →+* K)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) [IsSeparated f]
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    {AK : Scheme.{u}} (aK : AK ⟶ A) (xK : AK ⟶ Spec (CommRingCat.of K))
    (haK : IsPullback aK xK f (Spec.map (CommRingCat.ofHom r))) :
    ∃ (p₁ p₂ : pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ⟶ AK)
      (eK : Spec (CommRingCat.of K) ⟶ AK)
      (iX iY : AK ⟶ pullback (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))),
      p₁ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.fst f f ∧
      p₁ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      p₂ ≫ aK = pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ≫ pullback.snd f f ∧
      p₂ ≫ xK = pullback.snd (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r)) ∧
      IsPullback p₁ p₂ xK xK ∧
      eK ≫ aK = Spec.map (CommRingCat.ofHom r) ≫ e ∧ eK ≫ xK = 𝟙 _ ∧
      IsClosedImmersion iX ∧ iX ≫ p₁ = 𝟙 AK ∧ iX ≫ p₂ = xK ≫ eK ∧
      iX ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (𝟙 A) (f ≫ e) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) ∧
      IsClosedImmersion iY ∧ iY ≫ p₁ = xK ≫ eK ∧ iY ≫ p₂ = 𝟙 AK ∧
      iY ≫ pullback.fst (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom r))
        = aK ≫ pullback.lift (f ≫ e) (𝟙 A) (by rw [Category.id_comp, Category.assoc, he, Category.comp_id]) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isPullback_fibre_prod_and_slices_of_section.solution
