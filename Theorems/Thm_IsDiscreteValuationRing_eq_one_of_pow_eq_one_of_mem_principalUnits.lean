import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits

set_option autoImplicit false
open IsLocalRing
theorem IsDiscreteValuationRing.eq_one_of_pow_eq_one_of_mem_principalUnits {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R]
    {n : ℕ} {e : ℕ} (hne : Ideal.span {(n : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {ζ : Rˣ} (hζ : ζ ∈ principalUnits R k) (hζn : ζ ^ n = 1) : ζ = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_eq_one_of_pow_eq_one_of_mem_principalUnits.solution
