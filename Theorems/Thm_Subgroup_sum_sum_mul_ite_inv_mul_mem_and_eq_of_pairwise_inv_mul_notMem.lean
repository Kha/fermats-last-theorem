import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem

set_option autoImplicit false
open scoped Classical in

theorem Subgroup.sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem
    {G : Type*} [Group G] (A V : Subgroup G) (Fa Ft : Finset G) (c : G → G → ℂ)
    (hFa : ∀ α ∈ Fa, ∀ α' ∈ Fa, α ≠ α' → α⁻¹ * α' ∉ A)
    (hFt : ∀ τ ∈ Ft, ∀ τ' ∈ Ft, τ ≠ τ' → τ⁻¹ * τ' ∉ V)
    (a t α τ : G) (hα : α ∈ Fa) (hτ : τ ∈ Ft) (hA : a⁻¹ * α ∈ A) (hV : t⁻¹ * τ ∈ V) :
    (∑ α' ∈ Fa, ∑ τ' ∈ Ft, c α' τ' * (if a⁻¹ * α' ∈ A ∧ t⁻¹ * τ' ∈ V then 1 else 0)) = c α τ := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_sum_sum_mul_ite_inv_mul_mem_and_eq_of_pairwise_inv_mul_notMem.solution
