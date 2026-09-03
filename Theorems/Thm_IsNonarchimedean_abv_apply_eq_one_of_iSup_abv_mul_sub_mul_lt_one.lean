import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_IsNonarchimedean_abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one

set_option autoImplicit false

open AlgebraicCurve

theorem IsNonarchimedean.abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (x v : Fin r → K) (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) (hv1 : ∃ j, μ (v j) = 1)
    (hlt : (⨆ p : Fin r × Fin r, μ (x p.1 * v p.2 - x p.2 * v p.1)) < 1)
    (i : Fin r) (hi : μ (x i) = 1) : μ (v i) = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsNonarchimedean_abv_apply_eq_one_of_iSup_abv_mul_sub_mul_lt_one.solution
