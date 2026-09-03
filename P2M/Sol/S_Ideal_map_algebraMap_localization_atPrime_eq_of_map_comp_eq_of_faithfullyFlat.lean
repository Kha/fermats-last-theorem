import Mathlib
import P2M.Util
namespace P2MW.S_Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat

set_option autoImplicit false

theorem solution
    {R S : Type} [CommRing R] [CommRing S] (𝔭 : Ideal R) [𝔭.IsPrime]
    (ψ : Localization.AtPrime 𝔭 →+* S)
    (hψ : letI : Algebra (Localization.AtPrime 𝔭) S := ψ.toAlgebra;
      Module.FaithfullyFlat (Localization.AtPrime 𝔭) S)
    (I J : Ideal R)
    (h : I.map (ψ.comp (algebraMap R (Localization.AtPrime 𝔭))) = J.map (ψ.comp (algebraMap R (Localization.AtPrime 𝔭)))) :
    I.map (algebraMap R (Localization.AtPrime 𝔭)) = J.map (algebraMap R (Localization.AtPrime 𝔭)) := by
  letI inst : Algebra (Localization.AtPrime 𝔭) S := ψ.toAlgebra
  haveI : Module.FaithfullyFlat (Localization.AtPrime 𝔭) S := hψ
  have hψeq : ψ = algebraMap (Localization.AtPrime 𝔭) S := rfl
  have h' : (I.map (algebraMap R (Localization.AtPrime 𝔭))).map (algebraMap (Localization.AtPrime 𝔭) S) =
      (J.map (algebraMap R (Localization.AtPrime 𝔭))).map (algebraMap (Localization.AtPrime 𝔭) S) := by
    rw [Ideal.map_map, Ideal.map_map, ← hψeq]; exact h
  have := congrArg (Ideal.comap (algebraMap (Localization.AtPrime 𝔭) S)) h'
  simpa only [Ideal.comap_map_eq_self_of_faithfullyFlat] using this
