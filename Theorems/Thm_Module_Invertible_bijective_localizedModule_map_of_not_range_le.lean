import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_bijective_localizedModule_map_of_not_range_le

set_option autoImplicit false

theorem Module.Invertible.bijective_localizedModule_map_of_not_range_le
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q) (x : PrimeSpectrum R)
    (hx : ¬ LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q)) :
    Function.Bijective (LocalizedModule.map x.asIdeal.primeCompl f) := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_bijective_localizedModule_map_of_not_range_le.solution
