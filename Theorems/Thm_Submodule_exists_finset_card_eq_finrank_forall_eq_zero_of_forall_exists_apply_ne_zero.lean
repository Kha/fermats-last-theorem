import Mathlib
import P2M.Util
import P2M.Sol.S_Submodule_exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero

set_option autoImplicit false

theorem Submodule.exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
    (f : ∀ i, V →ₗ[k] W i) (D : Submodule k V) [FiniteDimensional k D]
    (good : Set ι)
    (hpad : ∀ T : Finset ι, ∃ i ∈ good, i ∉ T)
    (hkill : ∀ ψ ∈ D, ψ ≠ 0 → ∀ T : Finset ι, ∃ i ∈ good, i ∉ T ∧ f i ψ ≠ 0)
    (T₀ : Finset ι) :
    ∃ Q : Finset ι, ↑Q ⊆ good ∧ Disjoint Q T₀ ∧ Q.card = Module.finrank k D ∧
      ∀ ψ ∈ D, (∀ i ∈ Q, f i ψ = 0) → ψ = 0 := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_finset_card_eq_finrank_forall_eq_zero_of_forall_exists_apply_ne_zero.solution
