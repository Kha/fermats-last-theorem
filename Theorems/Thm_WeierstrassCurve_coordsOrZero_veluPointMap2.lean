import Mathlib
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_coordsOrZero_veluPointMap2

set_option autoImplicit false

theorem WeierstrassCurve.coordsOrZero_veluPointMap2
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (h2 : (2 : F) ≠ 0)
    {x₀ y₀ : F} (hns : W.toAffine.Nonsingular x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (P : W.toAffine.Point)
    (hP : P ∉ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point)) :
    (WeierstrassCurve.veluPointMap2 h2 hns.1 hgy hΔ P).coordsOrZero =
      (P.coordsOrZero.1 + ∑ k ∈ Finset.Icc 1 (2 - 1),
          ((P + k • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point)).coordsOrZero.1 -
            (k • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point)).coordsOrZero.1),
       P.coordsOrZero.2 + ∑ k ∈ Finset.Icc 1 (2 - 1),
          ((P + k • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point)).coordsOrZero.2 -
            (k • (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : W.toAffine.Point)).coordsOrZero.2)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_coordsOrZero_veluPointMap2.solution
