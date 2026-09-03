import Mathlib
import P2M.Util
import P2M.Sol.S_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd

set_option autoImplicit false

theorem AddCircle.exists_eq_coe_div_of_nsmul_eq_zero_of_dvd
    (t : AddCircle (1 : ℚ)) (n N : ℕ) (hN : 0 < N) (hnN : n ∣ N) (ht : n • t = 0) :
    ∃ a : ℤ, t = (((a : ℚ) / (N : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_AddCircle_exists_eq_coe_div_of_nsmul_eq_zero_of_dvd.solution
