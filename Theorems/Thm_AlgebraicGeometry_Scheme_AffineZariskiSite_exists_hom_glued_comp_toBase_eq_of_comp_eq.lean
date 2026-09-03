import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.AffineZariskiSite.exists_hom_glued_comp_toBase_eq_of_comp_eq
    {Y : Scheme.{u}} {F₁ F₂ : Y.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α₁ : (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₁}
    {α₂ : (Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙ Y.presheaf ⟶ F₂}
    (H₁ : α₁.Coequifibered) (H₂ : α₂.Coequifibered) (β : F₂ ⟶ F₁) (hβ : α₂ ≫ β = α₁) :
    ∃ φ : (Scheme.AffineZariskiSite.relativeGluingData H₁).glued ⟶
        (Scheme.AffineZariskiSite.relativeGluingData H₂).glued,
      φ ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).toBase =
        (Scheme.AffineZariskiSite.relativeGluingData H₁).toBase ∧
      (∀ U : Y.AffineZariskiSite, (Scheme.AffineZariskiSite.relativeGluingData H₁).cover.f U ≫ φ =
        Spec.map (β.app (op U)) ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).cover.f U) ∧
      (∀ φ' : (Scheme.AffineZariskiSite.relativeGluingData H₁).glued ⟶
          (Scheme.AffineZariskiSite.relativeGluingData H₂).glued,
        (∀ U : Y.AffineZariskiSite, (Scheme.AffineZariskiSite.relativeGluingData H₁).cover.f U ≫ φ' =
          Spec.map (β.app (op U)) ≫ (Scheme.AffineZariskiSite.relativeGluingData H₂).cover.f U) →
        φ' = φ) ∧
      (IsIso β → IsIso φ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_exists_hom_glued_comp_toBase_eq_of_comp_eq.solution
