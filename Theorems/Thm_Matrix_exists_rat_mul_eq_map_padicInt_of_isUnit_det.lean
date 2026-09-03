import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det

theorem Matrix.exists_rat_mul_eq_map_padicInt_of_isUnit_det
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ_[p]) (hM : IsUnit M.det) :
    ∃ (Q : Matrix (Fin n) (Fin n) ℚ) (P : Matrix (Fin n) (Fin n) ℤ_[p]),
      IsUnit Q.det ∧ IsUnit P.det ∧
      M * Q.map (algebraMap ℚ ℚ_[p]) = P.map (algebraMap ℤ_[p] ℚ_[p]) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_rat_mul_eq_map_padicInt_of_isUnit_det.solution
