import Mathlib
import P2M.Util
import P2M.Sol.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun

set_option autoImplicit false

open Real Complex
open scoped Nat

theorem ZMod.tsum_intCast_pow_inv_eq_sum_bernoulliFun (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k)
    (a : ZMod N) :
    ∑' d : {d : ℤ // (d : ZMod N) = a}, ((d : ℂ) ^ k)⁻¹ =
      -(2 * π * I) ^ k / (k ! * N) *
        ∑ r : ZMod N, ZMod.stdAddChar (-(r * a)) * (bernoulliFun k ((r.val : ℝ) / N) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ZMod_tsum_intCast_pow_inv_eq_sum_bernoulliFun.solution
