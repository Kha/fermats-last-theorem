import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_relIndex_principalUnits_succ

set_option autoImplicit false
open IsLocalRing
theorem IsDiscreteValuationRing.relIndex_principalUnits_succ {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) :
    (principalUnits R (k + 1)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_relIndex_principalUnits_succ.solution
