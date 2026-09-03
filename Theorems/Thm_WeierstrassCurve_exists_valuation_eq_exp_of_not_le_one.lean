import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one

theorem WeierstrassCurve.exists_valuation_eq_exp_of_not_le_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
    ∃ s : ℕ, 0 < s ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x = WithZero.exp (2 * (s : ℤ)) ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y = WithZero.exp (3 * (s : ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_valuation_eq_exp_of_not_le_one.solution
