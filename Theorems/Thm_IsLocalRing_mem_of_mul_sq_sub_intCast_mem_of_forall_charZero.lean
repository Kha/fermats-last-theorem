import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero

set_option autoImplicit false

theorem IsLocalRing.mem_of_mul_sq_sub_intCast_mem_of_forall_charZero
    {R : Type} [CommRing R] [IsLocalRing R] (r : R) (d : ℤ)
    (hmax : r ∈ IsLocalRing.maximalIdeal R)
    (hquad : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → r * (r ^ 2 - (d : R)) ∈ 𝔭)
    (hzero : ∀ 𝔭 : Ideal R, 𝔭.IsPrime → CharZero (R ⧸ 𝔭) → r ∈ 𝔭)
    (𝔭 : Ideal R) (h𝔭 : 𝔭.IsPrime) : r ∈ 𝔭 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_mem_of_mul_sq_sub_intCast_mem_of_forall_charZero.solution
