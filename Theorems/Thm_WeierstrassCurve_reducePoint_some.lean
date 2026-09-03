import Mathlib
import Definitions.Def_EllipticCurve_PointReduction
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_reducePoint_some

theorem WeierstrassCurve.reducePoint_some
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1)
    (hy : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1) :
    ∃ h', WeierstrassCurve.reducePoint_alt R W (.some x y h)
      = .some (WeierstrassCurve.reduceCoord R x) (WeierstrassCurve.reduceCoord R y) h' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_reducePoint_some.solution
