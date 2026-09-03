import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_IsLocalRing_principalUnits_one_eq_ker_map_residue

set_option autoImplicit false
open IsLocalRing
theorem IsLocalRing.principalUnits_one_eq_ker_map_residue {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 1 = (Units.map (residue R : R →* ResidueField R)).ker := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_principalUnits_one_eq_ker_map_residue.solution
