import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq

set_option autoImplicit false
open IsLocalRing
theorem IsDiscreteValuationRing.exists_mem_principalUnits_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {n : ℕ} (hn : 0 < n) {e : ℕ} (hne : Ideal.span {(n : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) {w : Rˣ} (hw : w ∈ principalUnits R (k + e)) :
    ∃ u ∈ principalUnits R k, u ^ n = w := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_mem_principalUnits_pow_eq.solution
