import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_prox_smul_smul

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.prox_smul_smul
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {r : ℕ}
    (x v : Fin r → K) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) ≠ 0) :
    prox μ (c • x) (d • v) = prox μ x v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_prox_smul_smul.solution
