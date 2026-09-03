import Mathlib
import P2M.Util
import P2M.Sol.S_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one

set_option autoImplicit false

theorem EulerProduct.three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
    {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i)
    (c c₂ : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1) (hc₂ : ∀ i, ‖c₂ i‖ ≤ 1)
    (hcc : ∀ i, c i = 0 ∨ c₂ i = c i ^ 2)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ))
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv (fun z : ℂ => ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-z))⁻¹) (σ : ℂ) /
              ∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      + 4 * (-(deriv (fun z : ℂ => ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + t * Complex.I) /
              ∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + t * Complex.I)))⁻¹)).re
      + (-(deriv (fun z : ℂ => ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-z))⁻¹)
                ((σ : ℂ) + 2 * t * Complex.I) /
              ∏' i, (1 - c₂ i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * t * Complex.I)))⁻¹)).re := by p2m_exact_reverting @_root_.P2MW.S_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one.solution
