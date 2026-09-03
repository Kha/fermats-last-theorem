import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_IsLocalRing_principalUnits_one_eq_ker_map_residue
import P2M.Util
namespace P2MW.S_IsLocalRing_index_principalUnits_one

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R] :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ := by
  have hsurj : Function.Surjective (Units.map (residue R : R →* ResidueField R)) :=
    surjective_units_map_of_local_ringHom _ residue_surjective inferInstance
  rw [IsLocalRing.principalUnits_one_eq_ker_map_residue, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
