import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_sq_eq_one_iff_of_isUnit_two

set_option autoImplicit false

theorem IsLocalRing.sq_eq_one_iff_of_isUnit_two {R : Type} [CommRing R] [IsLocalRing R]
    (h2 : IsUnit (2 : R)) (u : R) : u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_sq_eq_one_iff_of_isUnit_two.solution
