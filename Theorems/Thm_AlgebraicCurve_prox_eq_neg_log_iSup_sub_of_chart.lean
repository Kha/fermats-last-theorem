import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart

open AlgebraicCurve

theorem AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j : Fin r) (hxj : x j = 1) (hyj : y j = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hy : ∀ i, ν (y i) ≤ 1) :
    prox ν x y = -Real.log (⨆ i, ν (x i - y i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart.solution
