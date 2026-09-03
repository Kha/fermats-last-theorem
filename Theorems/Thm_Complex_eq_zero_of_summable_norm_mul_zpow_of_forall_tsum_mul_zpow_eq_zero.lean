import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero

set_option autoImplicit false

theorem Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
    (e : ℤ → ℂ) {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (hs₁ : Summable fun m : ℤ => ‖e m‖ * r₁ ^ m) (hs₂ : Summable fun m : ℤ => ‖e m‖ * r₂ ^ m)
    (hz : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → ∑' m : ℤ, e m * z ^ m = 0) : e = 0 := by p2m_exact_reverting @_root_.P2MW.S_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero.solution
