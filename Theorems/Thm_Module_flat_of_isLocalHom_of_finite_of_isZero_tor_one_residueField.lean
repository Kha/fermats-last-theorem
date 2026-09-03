import Mathlib
import P2M.Util
import P2M.Sol.S_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField

universe u v

open CategoryTheory CategoryTheory.Limits IsLocalRing

theorem Module.flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField.solution
