import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_ringHom_ext_padicInt

set_option autoImplicit false

open scoped PadicInt

universe u

theorem WittVector.ringHom_ext_padicInt
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]
    (f g : ℤ_[p] →+* WittVector p R) : f = g := by p2m_exact_reverting @_root_.P2MW.S_WittVector_ringHom_ext_padicInt.solution
