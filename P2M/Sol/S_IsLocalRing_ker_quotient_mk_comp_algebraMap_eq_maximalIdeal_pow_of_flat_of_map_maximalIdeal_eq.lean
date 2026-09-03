import Mathlib
import P2M.Util
namespace P2MW.S_IsLocalRing_ker_quotient_mk_comp_algebraMap_eq_maximalIdeal_pow_of_flat_of_map_maximalIdeal_eq

set_option autoImplicit false

theorem solution
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S) (k : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal S ^ k)).comp (algebraMap R S)) =
      IsLocalRing.maximalIdeal R ^ k := by
  haveI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← hmax, ← Ideal.map_pow]
  exact Ideal.comap_map_eq_self_of_faithfullyFlat _
