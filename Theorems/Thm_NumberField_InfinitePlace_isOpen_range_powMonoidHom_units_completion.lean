import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_isOpen_range_powMonoidHom_units_completion

set_option autoImplicit false
theorem NumberField.InfinitePlace.isOpen_range_powMonoidHom_units_completion {K : Type*} [Field K]
    (w : NumberField.InfinitePlace K) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range : Set (w.Completion)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_isOpen_range_powMonoidHom_units_completion.solution
