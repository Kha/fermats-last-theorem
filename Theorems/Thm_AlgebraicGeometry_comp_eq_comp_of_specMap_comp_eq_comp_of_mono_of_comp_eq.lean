import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq
    {A Q : Type u} [CommRing A] [CommRing Q] (π : A →+* Q)
    {Y K : Scheme.{u}} (ι : Spec (CommRingCat.of A) ⟶ Y) [Mono ι] (k₁ : K ⟶ Y)

    (pr : Spec (CommRingCat.of Q) ⟶ K)
    (hpr : Spec.map (CommRingCat.ofHom π) ≫ ι = pr ≫ k₁)

    (E₁ E₂ : Y ⟶ Y) (f₁ f₂ : A →+* A)
    (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ ι = ι ≫ E₁)
    (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ ι = ι ≫ E₂)

    (hK : k₁ ≫ E₁ = k₁ ≫ E₂) :
    π.comp f₁ = π.comp f₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq.solution
