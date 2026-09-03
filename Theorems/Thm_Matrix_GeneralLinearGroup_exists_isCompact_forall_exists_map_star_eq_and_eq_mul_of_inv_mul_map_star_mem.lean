import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem
    (B : Set (Matrix (Fin 2) (Fin 2) ℂ)) (hB : IsCompact B) :
    ∃ K : Set (GL (Fin 2) ℂ), IsCompact K ∧
      ∀ x : GL (Fin 2) ℂ,
        ((x⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) ∈ B →
        ∃ m k : GL (Fin 2) ℂ,
          ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = m ∧ k ∈ K ∧ x = m * k := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_isCompact_forall_exists_map_star_eq_and_eq_mul_of_inv_mul_map_star_mem.solution
