module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log

@[expose] public section
open AlgebraicCurve
theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f = -WithZero.log (w.valuation (RatFunc K) f) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log.solution
