import Mathlib
import Definitions.Def_EllipticCurve_PointReduction
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_reducePoint_some_eq_zero_iff

theorem WeierstrassCurve.reducePoint_some_eq_zero_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y) :
    WeierstrassCurve.reducePoint_alt R W (.some x y h) = .zero ↔
      ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_reducePoint_some_eq_zero_iff.solution
