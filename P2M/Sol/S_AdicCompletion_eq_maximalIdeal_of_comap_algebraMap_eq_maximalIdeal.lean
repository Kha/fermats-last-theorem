import Mathlib
import Definitions.Def_AdicCompletionLocalRing
import P2M.Util
namespace P2MW.S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) P = maximalIdeal R) :
    P = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
  have hle : maximalIdeal (AdicCompletion (maximalIdeal R) R) ≤ P := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hP]
  exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
