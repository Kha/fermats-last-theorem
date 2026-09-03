import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_finite_setOf_height_eq_one_and_mem

set_option autoImplicit false
theorem Ideal.finite_setOf_height_eq_one_and_mem
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {b : R} (hb : b ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ b ∈ p}.Finite := by p2m_exact_reverting @_root_.P2MW.S_Ideal_finite_setOf_height_eq_one_and_mem.solution
