module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
import P2M.Util
public import Mathlib
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.Def_AlgebraicCurve_RatFuncPlaces
public import Definitions.Def_AlgebraicCurve_PlaceEvaluation
public import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  by_cases h : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w
  · exact Or.inr ((AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum v).2 h)
  · push_neg at h
    exact Or.inl h
end S_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
end P2MW

public section
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty
end
