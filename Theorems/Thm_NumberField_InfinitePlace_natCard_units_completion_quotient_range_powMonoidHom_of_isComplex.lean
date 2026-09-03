import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex

set_option autoImplicit false
theorem NumberField.InfinitePlace.natCard_units_completion_quotient_range_powMonoidHom_of_isComplex {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) {n : ℕ} (hn : 0 < n) :
    Nat.card ((w.Completion)ˣ ⧸ (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range) = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_natCard_units_completion_quotient_range_powMonoidHom_of_isComplex.solution
