import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Opposite

theorem AlgebraicCurve.CurveModel.germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq
    {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] (M : CurveModel K L)
    {Y : Scheme.{u}} [IsIntegral Y] (φ : Y ⟶ M.C) (hφ : φ.base (genericPoint Y) = genericPoint M.C)
    (j : L →+* Y.functionField)
    (hpin : ∀ (x : L) (U : M.C.Opens) (hU : genericPoint M.C ∈ U) (hU' : genericPoint Y ∈ φ ⁻¹ᵁ U)
        (sec : M.C.presheaf.obj (op U)),
        (M.C.presheaf.germ U (genericPoint M.C) hU).hom sec = M.ffEquiv x →
        (Y.presheaf.germ (φ ⁻¹ᵁ U) (genericPoint Y) hU').hom ((φ.app U).hom sec) = j x)
    (V : L ≃ₐ[K] L) (h : M.C ⟶ M.C)
    (hh : M.C.fromSpecStalk (genericPoint M.C) ≫ h =
      Spec.map (CommRingCat.ofHom
        (M.ffEquiv.toRingHom.comp ((V : L →ₐ[K] L).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
        M.C.fromSpecStalk (genericPoint M.C))
    (a : Y ⟶ Y) (ha₀ : a.base (genericPoint Y) = genericPoint Y) (ha : a ≫ φ = φ ≫ h) :
    ∀ (x : L) (U : Y.Opens) (hU : genericPoint Y ∈ U) (hU' : genericPoint Y ∈ a ⁻¹ᵁ U)
      (sec : Y.presheaf.obj (op U)),
      (Y.presheaf.germ U (genericPoint Y) hU).hom sec = j x →
      (Y.presheaf.germ (a ⁻¹ᵁ U) (genericPoint Y) hU').hom ((a.app U).hom sec) = j (V x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_germ_app_eq_of_germ_eq_of_comp_eq_comp_of_fromSpecStalk_comp_eq.solution
