import Mathlib.Analysis.SpecialFunctions.Pow.Real
import P2M.Util
import P2M.Sol.S_RegularSingular_expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le

set_option autoImplicit false

theorem RegularSingular.expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (e₁ : ι₁ → ℂ) (n₁ : ι₁ → ℕ) (h₁ : Function.Injective fun i => (e₁ i, n₁ i))
    (e₂ : ι₂ → ℂ) (n₂ : ι₂ → ℕ) (h₂ : Function.Injective fun k => (e₂ k, n₂ k))
    (c₁ : ι₁ → ℂ) (c₂ : ι₂ → ℂ) (θ : ℝ) (F : ℝ → ℂ)
    (hF₁ : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ i, c₁ i * ((y : ℂ) ^ e₁ i * (Real.log y : ℂ) ^ n₁ i)‖ ≤ K * y ^ θ)
    (hF₂ : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖F y - ∑ k, c₂ k * ((y : ℂ) ^ e₂ k * (Real.log y : ℂ) ^ n₂ k)‖ ≤ K * y ^ θ) :
    (∀ i k, e₁ i = e₂ k → n₁ i = n₂ k → (e₁ i).re < θ → c₁ i = c₂ k) ∧
    (∀ i, (e₁ i).re < θ → (∀ k, (e₂ k, n₂ k) ≠ (e₁ i, n₁ i)) → c₁ i = 0) ∧
    (∀ k, (e₂ k).re < θ → (∀ i, (e₁ i, n₁ i) ≠ (e₂ k, n₂ k)) → c₂ k = 0) := by p2m_exact_reverting @_root_.P2MW.S_RegularSingular_expLogSum_coeff_eq_of_norm_sub_sum_le_of_norm_sub_sum_le.solution
