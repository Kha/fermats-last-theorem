import Mathlib
import Theorems.Thm_Submodule_iInf_sup_pow_smul_top_eq_of_le_jacobson
import P2M.Util
namespace P2MW.S_Submodule_mem_of_forall_exists_sub_mem_pow_smul_top

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M]
    (N : Submodule ℤ_[p] M) (x : M)
    (h : ∀ n : ℕ, ∃ a ∈ N, x - a ∈ ((p : ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] M))) : x ∈ N := by
  have hI : (Ideal.span {(p : ℤ_[p])} : Ideal ℤ_[p]) ≤ Ideal.jacobson ⊥ := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  rw [← Submodule.iInf_sup_pow_smul_top_eq_of_le_jacobson (Ideal.span {(p : ℤ_[p])}) hI N, Submodule.mem_iInf]
  intro n
  obtain ⟨a, ha, hxa⟩ := h n
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  have : x = a + (x - a) := by abel
  rw [this]
  exact Submodule.add_mem_sup ha hxa
