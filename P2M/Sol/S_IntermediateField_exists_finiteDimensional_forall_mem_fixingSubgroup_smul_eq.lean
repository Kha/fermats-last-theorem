import Mathlib
import Theorems.Thm_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
import P2M.Util
namespace P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq

set_option autoImplicit false

universe u v

open IntermediateField

theorem solution
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ωˣ) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ • x = x := by
  obtain ⟨E, hE, h⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq (K := K) (x : Ω)
  exact ⟨E, hE, fun σ hσ => Units.ext (h σ hσ)⟩
