import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_index_principalUnits_one

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.index_principalUnits_one {R : Type*} [CommRing R] [IsLocalRing R] :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_index_principalUnits_one.solution
