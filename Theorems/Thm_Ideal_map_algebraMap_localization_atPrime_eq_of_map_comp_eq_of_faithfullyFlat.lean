import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat

set_option autoImplicit false

theorem Ideal.map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat
    {R S : Type} [CommRing R] [CommRing S] (𝔭 : Ideal R) [𝔭.IsPrime]
    (ψ : Localization.AtPrime 𝔭 →+* S)
    (hψ : letI : Algebra (Localization.AtPrime 𝔭) S := ψ.toAlgebra;
      Module.FaithfullyFlat (Localization.AtPrime 𝔭) S)
    (I J : Ideal R)
    (h : I.map (ψ.comp (algebraMap R (Localization.AtPrime 𝔭))) = J.map (ψ.comp (algebraMap R (Localization.AtPrime 𝔭)))) :
    I.map (algebraMap R (Localization.AtPrime 𝔭)) = J.map (algebraMap R (Localization.AtPrime 𝔭)) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat.solution
