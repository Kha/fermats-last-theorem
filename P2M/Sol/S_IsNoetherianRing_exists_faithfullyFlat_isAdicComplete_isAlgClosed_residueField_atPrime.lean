import Mathlib
import Theorems.Thm_IsLocalRing_exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
import Theorems.Thm_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
import P2M.Util
namespace P2MW.S_IsNoetherianRing_exists_faithfullyFlat_isAdicComplete_isAlgClosed_residueField_atPrime
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem solution
    (S : Type) [CommRing S] [IsNoetherianRing S] (𝔭 : PrimeSpectrum S) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) (_ : IsAlgClosed (IsLocalRing.ResidueField R))
      (_ : Algebra S R) (_ : Algebra (Localization.AtPrime 𝔭.asIdeal) R)
      (_ : IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) R),
      Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) R := by
  classical

  obtain ⟨B, _, _, _, _, _, hff, hmap, ⟨eK⟩⟩ :=
    IsLocalRing.exists_isNoetherianRing_faithfullyFlat_map_maximalIdeal_eq_residueField_algEquiv_of_isAlgebraic
      (Localization.AtPrime 𝔭.asIdeal)
      (AlgebraicClosure (ResidueField (Localization.AtPrime 𝔭.asIdeal)))

  obtain ⟨hloc, hnoeth, hcompl, hmax, hsurj, hker, -⟩ :=
    AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing B (maximalIdeal B)

  haveI hlh : IsLocalHom (algebraMap B (AdicCompletion (maximalIdeal B) B)) :=
    ((local_hom_TFAE (algebraMap B (AdicCompletion (maximalIdeal B) B))).out 0 2).mpr hmax.symm.le
  haveI hffB : Module.FaithfullyFlat B (AdicCompletion (maximalIdeal B) B) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI hffA : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) B := hff
  haveI hstAB : IsScalarTower (Localization.AtPrime 𝔭.asIdeal) B (AdicCompletion (maximalIdeal B) B) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hffAR : Module.FaithfullyFlat (Localization.AtPrime 𝔭.asIdeal) (AdicCompletion (maximalIdeal B) B) :=
    Module.FaithfullyFlat.trans (Localization.AtPrime 𝔭.asIdeal) B (AdicCompletion (maximalIdeal B) B)

  letI algSB : Algebra S B :=
    ((algebraMap (Localization.AtPrime 𝔭.asIdeal) B).comp (algebraMap S (Localization.AtPrime 𝔭.asIdeal))).toAlgebra
  haveI hstSA : IsScalarTower S (Localization.AtPrime 𝔭.asIdeal) (AdicCompletion (maximalIdeal B) B) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hBac : IsAlgClosed (ResidueField B) :=
    IsAlgClosed.of_ringEquiv (k := AlgebraicClosure (ResidueField (Localization.AtPrime 𝔭.asIdeal)))
      (ResidueField B) eK.symm.toRingEquiv
  have e1 : B ⧸ RingHom.ker ((residue (AdicCompletion (maximalIdeal B) B)).comp
      (algebraMap B (AdicCompletion (maximalIdeal B) B))) ≃+* ResidueField (AdicCompletion (maximalIdeal B) B) :=
    RingHom.quotientKerEquivOfSurjective hsurj
  have e2 : ResidueField B ≃+* B ⧸ RingHom.ker ((residue (AdicCompletion (maximalIdeal B) B)).comp
      (algebraMap B (AdicCompletion (maximalIdeal B) B))) :=
    Ideal.quotEquivOfEq hker.symm
  have hRac : IsAlgClosed (ResidueField (AdicCompletion (maximalIdeal B) B)) :=
    IsAlgClosed.of_ringEquiv (k := ResidueField B) _ (e2.trans e1)
  exact ⟨AdicCompletion (maximalIdeal B) B, inferInstance, hloc, hnoeth, hcompl, hRac,
    inferInstance, inferInstance, hstSA, hffAR⟩
