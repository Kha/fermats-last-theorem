import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_mem_of_forall_exists_sub_mem_pow_smul_top

set_option autoImplicit false

open scoped Pointwise

theorem Submodule.mem_of_forall_exists_sub_mem_pow_smul_top
    {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (N : Submodule ℤ_[p] M) (x : M)
    (h : ∀ n : ℕ, ∃ a ∈ N, x - a ∈ ((p : ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] M))) : x ∈ N := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_of_forall_exists_sub_mem_pow_smul_top.solution
