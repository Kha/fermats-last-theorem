import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2

theorem WeierstrassCurve.fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (h2 : (2 : F) ≠ 0) {m : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * (m + 1))
    {x₀ y₀ : F} {h₀ : W.toAffine.Nonsingular x₀ y₀}
    (hT : (m + 1) • Q = Affine.Point.some x₀ y₀ h₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) :
    W.fullKernelQuotient Q (2 * (m + 1)) =
      (W.veluQuotient2 x₀ y₀).fullKernelQuotient (veluPointMap2 h2 h₀.1 hgy hΔ Q) (m + 1) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_fullKernelQuotient_eq_fullKernelQuotient_veluQuotient2.solution
