import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
    {K : Type u} [Field K] {L L' : Type v} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    (e : L ≃ₐ[K] L') (M : AlgebraicCurve.CurveModel K L) :
    ∃ (M' : AlgebraicCurve.CurveModel K L') (f : M'.C ≅ M.C), f.hom ≫ M.toBase = M'.toBase ∧
      ∀ (V : M.C.Opens) [Nonempty (Scheme.Opens.toScheme V)] [Nonempty (Scheme.Opens.toScheme (f.hom ⁻¹ᵁ V))]
        (t : Γ(M.C, V)),
        M'.ffEquiv.symm (M'.C.germToFunctionField (f.hom ⁻¹ᵁ V) ((f.hom.app V).hom t)) =
          e (M.ffEquiv.symm (M.C.germToFunctionField V t)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv.solution
