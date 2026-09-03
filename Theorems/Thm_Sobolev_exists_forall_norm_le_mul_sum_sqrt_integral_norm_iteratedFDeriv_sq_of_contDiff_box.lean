import Mathlib
import P2M.Util
import P2M.Sol.S_Sobolev_exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box

set_option autoImplicit false

open MeasureTheory

theorem Sobolev.exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box
    (n : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (a : Fin n → ℝ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ n f →
      ∀ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (a i) (a i + ℓ)) →
        ‖f x‖ ≤ c * ∑ k ∈ Finset.range (n + 1),
          Real.sqrt (∫ y in Set.pi Set.univ (fun i => Set.Icc (a i) (a i + ℓ)), ‖iteratedFDeriv ℝ k f y‖ ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_Sobolev_exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box.solution
