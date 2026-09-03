import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.exists_mem_principalUnits_coe_sub_one_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} (hk : 1 ≤ k) {x : R} (hx : x ∈ maximalIdeal R ^ k) :
    ∃ u ∈ principalUnits R k, (u : R) - 1 = x := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_mem_principalUnits_coe_sub_one_eq.solution
