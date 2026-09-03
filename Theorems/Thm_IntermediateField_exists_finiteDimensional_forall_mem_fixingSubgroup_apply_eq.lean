import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq

set_option autoImplicit false

universe u v

open IntermediateField
theorem IntermediateField.exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (x : Ω) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → σ x = x := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_finiteDimensional_forall_mem_fixingSubgroup_apply_eq.solution
