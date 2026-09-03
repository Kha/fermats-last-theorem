import Mathlib
import Definitions.Def_EllipticCurve_PointReduction
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one

theorem WeierstrassCurve.reducePoint_some_add_some_of_not_le_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    [DecidableEq (IsLocalRing.ResidueField R)]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x₁ y₁ x₂ y₂ : K}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hx₁ : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x₁ ≤ 1)
    (hx₂ : ¬ IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x₂ ≤ 1) :
    WeierstrassCurve.reducePoint_alt R W (.some x₁ y₁ h₁ + .some x₂ y₂ h₂)
      = WeierstrassCurve.reducePoint_alt R W (.some x₁ y₁ h₁) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_reducePoint_some_add_some_of_not_le_one.solution
