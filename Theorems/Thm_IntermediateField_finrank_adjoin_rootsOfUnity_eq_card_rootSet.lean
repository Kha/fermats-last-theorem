import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet

set_option autoImplicit false
open IntermediateField
theorem IntermediateField.finrank_adjoin_rootsOfUnity_eq_card_rootSet {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E] [CharZero F] (m : ℕ) (hm : 0 < m) (ζ₀ : E)
    (hζ₀ : IsPrimitiveRoot ζ₀ m) :
    Module.finrank F (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1})
      = Fintype.card ((minpoly F ζ₀).rootSet E) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet.solution
