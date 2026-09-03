import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem
    {K : Type*} [Field K] (O : ValuationSubring K) (ϖ : K) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (g : GL (Fin 2) K)
    (hg : ∀ M : Matrix (Fin 2) (Fin 2) K, (∀ i j, M i j ∈ O) → ϖ⁻¹ * M 1 0 ∈ O →
      (∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i j ∈ O) ∧
        ϖ⁻¹ * ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 1 0 ∈ O) :
    ∃ c : Kˣ,
      ((∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
        ϖ⁻¹ * (((c⁻¹ : Kˣ) : K) * (g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ O ∧
        (∀ i j, (c : K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ O) ∧
        ϖ⁻¹ * ((c : K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ O) ∨
      ((∀ i j, ((!![0, ϖ⁻¹; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
          (((c⁻¹ : Kˣ) : K) • (g : Matrix (Fin 2) (Fin 2) K))) i j ∈ O) ∧
        ϖ⁻¹ * ((!![0, ϖ⁻¹; 1, 0] : Matrix (Fin 2) (Fin 2) K) *
          (((c⁻¹ : Kˣ) : K) • (g : Matrix (Fin 2) (Fin 2) K))) 1 0 ∈ O ∧
        (∀ i j, (((c : K) • ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          (!![0, 1; ϖ, 0] : Matrix (Fin 2) (Fin 2) K)) i j ∈ O) ∧
        ϖ⁻¹ * ((((c : K) • ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
          (!![0, 1; ϖ, 0] : Matrix (Fin 2) (Fin 2) K)) 1 0) ∈ O) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_inv_mul_mem_iwahori_or_atkinLehner_inv_mul_mem_of_forall_conj_mem.solution
