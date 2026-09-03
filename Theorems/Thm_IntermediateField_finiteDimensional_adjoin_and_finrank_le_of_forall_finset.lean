import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset

set_option autoImplicit false

theorem IntermediateField.finiteDimensional_adjoin_and_finrank_le_of_forall_finset
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E) (n : ℕ)
    (hS : ∀ s : Finset E, (↑s : Set E) ⊆ S →
      FiniteDimensional F ↥(IntermediateField.adjoin F (↑s : Set E)) ∧
        Module.finrank F ↥(IntermediateField.adjoin F (↑s : Set E)) ≤ n) :
    FiniteDimensional F ↥(IntermediateField.adjoin F S) ∧ Module.finrank F ↥(IntermediateField.adjoin F S) ≤ n := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_adjoin_and_finrank_le_of_forall_finset.solution
