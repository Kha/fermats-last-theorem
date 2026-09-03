import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_valuation_le_one_of_equation

theorem WeierstrassCurve.valuation_le_one_of_equation
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.IsIntegral R] {x y : K} (h : W.toAffine.Equation x y)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) :
    IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_valuation_le_one_of_equation.solution
