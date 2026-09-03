import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    ∃ (H : ((Scheme.AffineZariskiSite.toOpensFunctor Y).op.whiskerLeft f.c).Coequifibered)
      (e : X ≅ (Scheme.AffineZariskiSite.relativeGluingData H).glued),
      e.hom ≫ (Scheme.AffineZariskiSite.relativeGluingData H).toBase = f ∧
      ∀ U : Y.AffineZariskiSite, (f ⁻¹ᵁ U.1).ι ≫ e.hom =
        (f ⁻¹ᵁ U.1).toSpecΓ ≫ (Scheme.AffineZariskiSite.relativeGluingData H).cover.f U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_coequifibered_iso_glued_comp_toBase_eq_of_isAffineHom.solution
