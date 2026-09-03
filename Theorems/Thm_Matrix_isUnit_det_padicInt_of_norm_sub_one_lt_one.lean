import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one

theorem Matrix.isUnit_det_padicInt_of_norm_sub_one_lt_one
    (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Matrix (Fin n) (Fin n) ℤ_[p])
    (h : ∀ i j, ‖P i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) :
    IsUnit P.det := by p2m_exact_reverting @_root_.P2MW.S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one.solution
