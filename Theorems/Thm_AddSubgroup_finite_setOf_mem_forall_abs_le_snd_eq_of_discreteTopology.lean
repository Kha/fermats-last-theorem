import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology

set_option autoImplicit false

theorem AddSubgroup.finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology
    {r c : ℕ} (Λ : AddSubgroup ((Fin r → ℝ) × (Fin c → ℤ))) [DiscreteTopology Λ] (R : ℝ) (k₀ : Fin c → ℤ) :
    {γ : (Fin r → ℝ) × (Fin c → ℤ) | γ ∈ Λ ∧ (∀ i, |γ.1 i| ≤ R) ∧ γ.2 = k₀}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology.solution
