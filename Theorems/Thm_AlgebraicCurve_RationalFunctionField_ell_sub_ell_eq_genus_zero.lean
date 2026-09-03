import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

universe u

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.ell_sub_ell_eq_genus_zero
    (K : Type u) [Field K] [DecidableEq (RatFunc K)] (D : Divisor K (RatFunc K)) :
    (ell D : ℤ) - ell ((-2 : ℤ) • Finsupp.single (placeInfty K) (1 : ℤ) - D) =
      Divisor.degree D + 1 - ((0 : ℕ) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ell_sub_ell_eq_genus_zero.solution
