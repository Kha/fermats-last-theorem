import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid

set_option autoImplicit false

universe u

theorem Algebra.isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S] [Module.Free R S]
    (F : Type u) [Field F] [Algebra S F] [IsFractionRing S F] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [IsScalarTower R S F] [Algebra.IsSeparable K F]
    (x : Ideal S) [x.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime x)] :
    (Ideal.map (algebraMap S (Localization.AtPrime x)) ((1 / Submodule.traceDual R K (1 : Submodule S F) : Submodule S F).comap (Algebra.linearMap S F))).IsPrincipal := by p2m_exact_reverting @_root_.P2MW.S_Algebra_isPrincipal_map_comap_one_div_traceDual_of_uniqueFactorizationMonoid.solution
