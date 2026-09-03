import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
namespace P2MW.S_IsLocalRing_principalUnits_one_eq_ker_map_residue

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 1 = (Units.map (residue R : R →* ResidueField R)).ker := by
  ext u
  rw [mem_principalUnits_iff, pow_one, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    MonoidHom.coe_coe, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
