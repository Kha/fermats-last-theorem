import Mathlib
import P2M.Util
import P2M.Sol.S_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral

set_option autoImplicit false

theorem EisensteinSeries.tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral
    (N : ℕ) (hN : 3 ≤ N) :
    (∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹) ≠ 0 ∧
    ∃ a : ℕ,
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)) ∧
      IsIntegral ℤ ((N : ℂ) ^ a * (2 / (2 * Real.pi * Complex.I) ^ 3 *
        ∑' d : {d : ℤ // (d : ZMod N) = 1}, ((d : ℂ) ^ 3)⁻¹)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral.solution
