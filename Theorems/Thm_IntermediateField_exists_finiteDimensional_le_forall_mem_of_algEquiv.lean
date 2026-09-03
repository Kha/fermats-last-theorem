import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_finiteDimensional_le_forall_mem_of_algEquiv

set_option autoImplicit false

theorem IntermediateField.exists_finiteDimensional_le_forall_mem_of_algEquiv
    {F E : Type} [Field F] [Field E] [Algebra F E] (halg : Algebra.IsAlgebraic F E)
    (k₀ : IntermediateField F E) (τ : E ≃ₐ[F] E) (hk₀ : ∀ x : E, x ∈ k₀ → τ x ∈ k₀)
    (K : IntermediateField ↥k₀ E) (hK : FiniteDimensional ↥k₀ ↥K) :
    ∃ K' : IntermediateField ↥k₀ E, FiniteDimensional ↥k₀ ↥K' ∧ K ≤ K' ∧ ∀ x : E, x ∈ K' → τ x ∈ K' := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_finiteDimensional_le_forall_mem_of_algEquiv.solution
