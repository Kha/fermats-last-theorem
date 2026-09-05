module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log
import P2M.Util

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span

set_option autoImplicit false

open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem solution {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log w hp hw
    (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]
end S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
end P2MW

public section
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span.solution
end
