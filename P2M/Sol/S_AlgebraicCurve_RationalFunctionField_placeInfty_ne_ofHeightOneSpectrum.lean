module

public import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import P2M.Util
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification -- shake: keep

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm
end S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
end P2MW

public section
open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.solution
#p2m_type_eq_warn P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum
end
