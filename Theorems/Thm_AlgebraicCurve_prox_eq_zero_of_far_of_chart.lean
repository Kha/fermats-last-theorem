import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_prox_eq_zero_of_far_of_chart

open AlgebraicCurve

theorem AlgebraicCurve.prox_eq_zero_of_far_of_chart {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j b : Fin r) (hxj : x j = 1) (hyb : y b = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hyj : ν (y j) < 1) :
    prox ν x y = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_prox_eq_zero_of_far_of_chart.solution
