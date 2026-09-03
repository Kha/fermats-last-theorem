import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable
set_option autoImplicit false
theorem IntermediateField.apply_mem_adjoin_simple_of_leibniz_of_isSeparable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : L → L) (hadd : ∀ a b : L, D (a + b) = D a + D b) (hmul : ∀ a b : L, D (a * b) = a * D b + b * D a)
    (F : IntermediateField K L) (hF : ∀ x : L, x ∈ F → D x ∈ F)
    (α : L) (hα : IsSeparable F α) (x : L) (hx : x ∈ IntermediateField.adjoin F ({α} : Set L)) :
    D x ∈ IntermediateField.adjoin F ({α} : Set L) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_apply_mem_adjoin_simple_of_leibniz_of_isSeparable.solution
