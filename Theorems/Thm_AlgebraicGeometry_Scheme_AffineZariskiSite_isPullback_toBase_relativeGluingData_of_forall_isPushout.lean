import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isPullback_toBase_relativeGluingData_of_forall_isPushout

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.AffineZariskiSite.isPullback_toBase_relativeGluingData_of_forall_isPushout
    {X : Scheme.{u}} {A : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ A} (H : α.Coequifibered)
    {X' Y : Scheme.{u}} (h : X' ⟶ X) [IsAffineHom h] (g : Y ⟶ X') [IsAffineHom g]
    (φ : Y ⟶ (Scheme.AffineZariskiSite.relativeGluingData H).glued)
    (hφ : φ ≫ (Scheme.AffineZariskiSite.relativeGluingData H).toBase = g ≫ h)

    (r : ∀ U : X.AffineZariskiSite, A.obj (op U) ⟶ Y.presheaf.obj (op (g ⁻¹ᵁ (h ⁻¹ᵁ U.1))))
    (hr : ∀ U : X.AffineZariskiSite,
      (g ⁻¹ᵁ (h ⁻¹ᵁ U.1)).ι ≫ φ =
        (g ⁻¹ᵁ (h ⁻¹ᵁ U.1)).toSpecΓ ≫ Spec.map (r U) ≫ (Scheme.AffineZariskiSite.relativeGluingData H).cover.f U)

    (hpo : ∀ U : X.AffineZariskiSite,
      IsPushout (α.app (op U)) (h.app U.1) (r U) (g.app (h ⁻¹ᵁ U.1))) :
    IsPullback φ g (Scheme.AffineZariskiSite.relativeGluingData H).toBase h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isPullback_toBase_relativeGluingData_of_forall_isPushout.solution
