import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le
    {ι : Type} [Fintype ι] (Θ : ι → ℝ → ℂ) (hΘ : ∀ i, Continuous (Θ i))
    (hΘg : ∀ i, ∃ (A : ℝ) (k : ℕ), ∀ t, ‖Θ i t‖ ≤ A * (1 + |t|) ^ k)
    (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hρm : ∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t))
    (hρ1 : ∫ t : ℝ, ρ t = 1)
    (M : ℝ)
    (h : ∀ (u : ι → ℝ → ℂ), (∀ i, Measurable (u i)) →
      (∃ R : ℝ, ∀ i x, R < |x| → u i x = 0) → (∃ B : ℝ, ∀ i x, ‖u i x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ‖∑ i, ∫ t : ℝ, conj (∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) * Θ i t‖ ≤
        M * Real.sqrt (∑ i, ∫ t : ℝ, ‖∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)‖ ^ 2)) :
    (∀ i, MemLp (Θ i) 2) ∧ ∑ i, ∫ t : ℝ, ‖Θ i t‖ ^ 2 ≤ M ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le.solution
