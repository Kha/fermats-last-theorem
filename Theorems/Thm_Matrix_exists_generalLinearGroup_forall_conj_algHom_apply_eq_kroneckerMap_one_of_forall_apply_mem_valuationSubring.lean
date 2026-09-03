import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring

set_option autoImplicit false

open scoped Kronecker

theorem Matrix.exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring
    (K : Type) [Field K] (𝒪 : ValuationSubring K) (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2 × n) (Fin 2 × n) K)
    (hρ : ∀ m : Matrix (Fin 2) (Fin 2) K, (∀ i j, m i j ∈ 𝒪) → ∀ i j, ρ m i j ∈ 𝒪) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 2 × n) K,
      (∀ i j, (P : Matrix (Fin 2 × n) (Fin 2 × n) K) i j ∈ 𝒪) ∧
      (∀ i j, ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2 × n) K) : Matrix (Fin 2 × n) (Fin 2 × n) K) i j ∈ 𝒪) ∧
      ∀ m : Matrix (Fin 2) (Fin 2) K,
        (P : Matrix (Fin 2 × n) (Fin 2 × n) K) * ρ m *
            ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 2 × n) K) : Matrix (Fin 2 × n) (Fin 2 × n) K) =
          Matrix.kroneckerMap (· * ·) m (1 : Matrix n n K) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_generalLinearGroup_forall_conj_algHom_apply_eq_kroneckerMap_one_of_forall_apply_mem_valuationSubring.solution
