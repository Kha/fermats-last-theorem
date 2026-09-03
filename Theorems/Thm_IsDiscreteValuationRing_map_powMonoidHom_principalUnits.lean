import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits

set_option autoImplicit false
open IsLocalRing
theorem IsDiscreteValuationRing.map_powMonoidHom_principalUnits {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : Ideal.span {(p : R)} = IsLocalRing.maximalIdeal R ^ e)
    {k : ℕ} (hk : e < k) :
    (principalUnits R k).map (powMonoidHom p) = principalUnits R (k + e) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_map_powMonoidHom_principalUnits.solution
