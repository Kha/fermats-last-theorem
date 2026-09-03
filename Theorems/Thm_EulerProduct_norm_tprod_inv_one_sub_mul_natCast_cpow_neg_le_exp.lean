import Mathlib
import P2M.Util
import P2M.Sol.S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp

set_option autoImplicit false

theorem EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) := by p2m_exact_reverting @_root_.P2MW.S_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp.solution
