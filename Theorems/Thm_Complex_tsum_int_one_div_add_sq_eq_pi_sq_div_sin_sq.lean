import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq

set_option autoImplicit false

open scoped MatrixGroups ModularForm Topology Real Matrix

theorem Complex.tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq (z : ℂ) (hz : z ∈ Complex.integerComplement) :
    ∑' n : ℤ, 1 / (z + n) ^ 2 = (π : ℂ) ^ 2 / Complex.sin (π * z) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_Complex_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq.solution
