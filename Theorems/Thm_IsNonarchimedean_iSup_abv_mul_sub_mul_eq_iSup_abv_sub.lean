import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_IsNonarchimedean_iSup_abv_mul_sub_mul_eq_iSup_abv_sub

set_option autoImplicit false

open AlgebraicCurve

theorem IsNonarchimedean.iSup_abv_mul_sub_mul_eq_iSup_abv_sub
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (i : Fin r) (hxi : x i = 1) (hvi : v i = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) = ⨆ l, μ (x l - v l) := by p2m_exact_reverting @_root_.P2MW.S_IsNonarchimedean_iSup_abv_mul_sub_mul_eq_iSup_abv_sub.solution
