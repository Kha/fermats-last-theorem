import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
    {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n K)
    (hg : ∀ M : Matrix n n K, (∀ i j, M i j ∈ 𝒪) →
      ∀ i j, ((g : Matrix n n K) * M * ((g⁻¹ : GL n K) : Matrix n n K)) i j ∈ 𝒪) :
    ∃ c : Kˣ, (∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix n n K) i j ∈ 𝒪) ∧
      (∀ i j, (c : K) * ((g⁻¹ : GL n K) : Matrix n n K) i j ∈ 𝒪) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem.solution
