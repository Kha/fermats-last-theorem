import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero

set_option autoImplicit false

open scoped TensorProduct

theorem Matrix.finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero
    {K : Type} [Field K] (T : Matrix (Fin 2) (Fin 2) K) (a b : K)
    (hT : (T - a • (1 : Matrix (Fin 2) (Fin 2) K)) * (T - b • (1 : Matrix (Fin 2) (Fin 2) K)) = 0) (hab : a ≠ b) :
    (Module.finrank K (LinearMap.ker (Matrix.mulVecLin (T - a • (1 : Matrix (Fin 2) (Fin 2) K)))) = 1 ∧
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin (T - b • (1 : Matrix (Fin 2) (Fin 2) K)))) = 1) ↔
    ((T - a • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 ∧ (T - b • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_finrank_ker_eq_one_and_iff_det_eq_zero_and_of_mul_eq_zero.solution
