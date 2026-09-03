import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_ringHom_eq_ringHom_of_isNilpotent

set_option autoImplicit false

universe u

theorem PadicInt.ringHom_eq_ringHom_of_isNilpotent (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (hB : IsNilpotent (p : B)) (f g : ℤ_[p] →+* B) : f = g := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_ringHom_eq_ringHom_of_isNilpotent.solution
