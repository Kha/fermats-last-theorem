import Definitions.Def_AlgebraicCurve_ChordalProximity
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {r : ℕ}
    (M Minv : Matrix (Fin r) (Fin r) K) (hM : Minv * M = 1)
    (β : ℝ) (hβ : 1 ≤ β) (hMβ : ∀ i j, μ (M i j) ≤ β) (hMβ' : ∀ i j, μ (Minv i j) ≤ β)
    (x y : Fin r → K) (hx : x ≠ 0) (hy : y ≠ 0) (h : ∃ i j, x i * y j - x j * y i ≠ 0) :
    |prox μ (M.mulVec x) (M.mulVec y) - prox μ x y| ≤ 4 * Real.log β := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le.solution
