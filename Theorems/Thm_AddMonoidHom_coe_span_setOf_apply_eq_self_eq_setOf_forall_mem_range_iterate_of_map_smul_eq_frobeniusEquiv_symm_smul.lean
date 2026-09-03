import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul

set_option autoImplicit false

theorem AddMonoidHom.coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (C : V →+ V) (hC : ∀ (a : K) (v : V), C (a • v) = (frobeniusEquiv K p).symm a • C v) :
    ((Submodule.span K {v : V | C v = v} : Submodule K V) : Set V) = {v : V | ∀ n : ℕ, v ∈ Set.range ((⇑C)^[n])} ∧
    ∀ n : ℕ, Module.finrank K V ≤ n → Set.range ((⇑C)^[n]) = {v : V | ∀ m : ℕ, v ∈ Set.range ((⇑C)^[m])} := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_coe_span_setOf_apply_eq_self_eq_setOf_forall_mem_range_iterate_of_map_smul_eq_frobeniusEquiv_symm_smul.solution
