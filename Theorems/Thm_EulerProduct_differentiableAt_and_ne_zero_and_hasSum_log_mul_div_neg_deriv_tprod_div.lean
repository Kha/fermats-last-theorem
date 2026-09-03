import Mathlib
import P2M.Util
import P2M.Sol.S_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div

set_option autoImplicit false

theorem EulerProduct.differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s ∧
    (∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 ∧
    HasSum (fun i => (Real.log (N i) : ℂ) * (c i * ((N i : ℕ) : ℂ) ^ (-s)) /
        (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))
      (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹) s /
          ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹)) := by p2m_exact_reverting @_root_.P2MW.S_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div.solution
