import Mathlib
import P2M.Util
import P2M.Sol.S_HeckeTreeWalk_cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow

set_option autoImplicit false

theorem HeckeTreeWalk.cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow
    (q : ℕ) (W : ℕ → ℕ → ℕ) (h00 : W 0 0 = 1) (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
    (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
    (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
    ∀ k : ℕ, (W (2 * k) 0 : ℤ) +
        ∑ r ∈ Finset.Icc 1 k, (W (2 * k) (2 * r) : ℤ) * ((q : ℤ) ^ r - (q : ℤ) ^ (r - 1)) =
      ((2 * k).choose k : ℤ) * (q : ℤ) ^ k := by p2m_exact_reverting @_root_.P2MW.S_HeckeTreeWalk_cast_walkCount_zero_add_sum_mul_pow_sub_pow_eq_centralBinom_mul_pow.solution
