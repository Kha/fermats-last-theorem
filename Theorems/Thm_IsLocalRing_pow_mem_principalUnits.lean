import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_pow_mem_principalUnits

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.pow_mem_principalUnits {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : (p : R) ∈ maximalIdeal R ^ e)
    {k : ℕ} {u : Rˣ} (hu : u ∈ principalUnits R k) :
    u ^ p ∈ principalUnits R (min (p * k) (k + e)) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_pow_mem_principalUnits.solution
