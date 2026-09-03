import Mathlib
import P2M.Util
import P2M.Sol.S_IsAdicComplete_of_isNilpotent

set_option autoImplicit false

universe u v

open IsLocalRing
theorem IsAdicComplete.of_isNilpotent {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R := by p2m_exact_reverting @_root_.P2MW.S_IsAdicComplete_of_isNilpotent.solution
