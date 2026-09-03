import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
theorem NumberField.isOpen_range_powMonoidHom_units_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range : Set (v.adicCompletion K)ˣ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_isOpen_range_powMonoidHom_units_adicCompletion.solution
