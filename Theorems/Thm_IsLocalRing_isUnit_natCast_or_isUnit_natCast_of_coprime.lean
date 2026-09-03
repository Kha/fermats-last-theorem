import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime

set_option autoImplicit false

theorem IsLocalRing.isUnit_natCast_or_isUnit_natCast_of_coprime
    {R : Type*} [CommRing R] [IsLocalRing R] {m n : ℕ} (h : Nat.Coprime m n) :
    IsUnit (m : R) ∨ IsUnit (n : R) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isUnit_natCast_or_isUnit_natCast_of_coprime.solution
