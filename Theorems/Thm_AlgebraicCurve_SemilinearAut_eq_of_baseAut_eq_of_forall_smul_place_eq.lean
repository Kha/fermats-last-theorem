import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

open AlgebraicCurve

universe u v

theorem AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (g g' : SemilinearAut K F) (hb : SemilinearAut.baseAut g = SemilinearAut.baseAut g')
    (h : ∀ v : Place K F, g • v = g' • v) : g = g' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq.solution
