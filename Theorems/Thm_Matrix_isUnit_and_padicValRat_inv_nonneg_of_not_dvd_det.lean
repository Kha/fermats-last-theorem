import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det

set_option autoImplicit false

theorem Matrix.isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det {m : Type*} [Fintype m] [DecidableEq m]
    (p : ℕ) [Fact p.Prime] (M : Matrix m m ℤ) (hM : ¬ (p : ℤ) ∣ M.det) :
    IsUnit (M.map (Int.cast : ℤ → ℚ)) ∧
      ∀ i j, 0 ≤ padicValRat p ((M.map (Int.cast : ℤ → ℚ))⁻¹ i j) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det.solution
