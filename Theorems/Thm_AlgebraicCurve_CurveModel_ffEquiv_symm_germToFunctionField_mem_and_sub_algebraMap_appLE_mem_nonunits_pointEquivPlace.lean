import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem AlgebraicCurve.CurveModel.ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] (s : Γ(M.C, U))
    (z : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (hz : ⊤ ≤ z.1 ⁻¹ᵁ U) :
    M.ffEquiv.symm (M.C.germToFunctionField U s) ∈ (M.pointEquivPlace z).toValuationSubring ∧
    M.ffEquiv.symm (M.C.germToFunctionField U s) -
        algebraMap K L ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (z.1.appLE U ⊤ hz s)) ∈
      (M.pointEquivPlace z).toValuationSubring.nonunits := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_germToFunctionField_mem_and_sub_algebraMap_appLE_mem_nonunits_pointEquivPlace.solution
