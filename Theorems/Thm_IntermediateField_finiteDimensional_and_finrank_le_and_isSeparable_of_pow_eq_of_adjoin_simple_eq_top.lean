import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top

set_option autoImplicit false

theorem IntermediateField.finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (n : ℕ) (hn : (n : F) ≠ 0) (a : E) (b : F) (hb : b ≠ 0) (hab : a ^ n = algebraMap F E b)
    (hgen : IntermediateField.adjoin F ({a} : Set E) = ⊤) :
    FiniteDimensional F E ∧ Module.finrank F E ≤ n ∧ Algebra.IsSeparable F E := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finiteDimensional_and_finrank_le_and_isSeparable_of_pow_eq_of_adjoin_simple_eq_top.solution
