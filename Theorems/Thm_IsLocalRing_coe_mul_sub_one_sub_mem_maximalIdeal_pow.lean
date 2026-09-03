import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_coe_mul_sub_one_sub_mem_maximalIdeal_pow

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.coe_mul_sub_one_sub_mem_maximalIdeal_pow {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} {u v : Rˣ} (hu : u ∈ principalUnits R k) (hv : v ∈ principalUnits R k) :
    ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) ∈ maximalIdeal R ^ (2 * k) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_coe_mul_sub_one_sub_mem_maximalIdeal_pow.solution
