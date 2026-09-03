import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import P2M.Util
namespace P2MW.S_GaloisRep_ratLocalizedAt_exists_specMap_comp_eq_fromSpecResidueField

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (s : Spec (CommRingCat.of ℤ)) (hs : s.asIdeal = Ideal.span {(ℓ : ℤ)}) :
    ∃ φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* (Spec (CommRingCat.of ℤ)).residueField s,
      Function.Surjective φ ∧ φ (ℓ : ↥(GaloisRep.ratLocalizedAt ℓ)) = 0 ∧
      Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ))) =
        (Spec (CommRingCat.of ℤ)).fromSpecResidueField s := by
  have hp : ℓ.Prime := Fact.out
  haveI hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  haveI : IsLocalization.AtPrime (GaloisRep.ratLocalizedAt ℓ) (Ideal.span {(ℓ : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt hp
  have hM : s.asIdeal.primeCompl = (Ideal.span {(ℓ : ℤ)}).primeCompl := by
    ext x
    show x ∈ s.asIdeal.primeCompl ↔ x ∈ (Ideal.span {(ℓ : ℤ)}).primeCompl
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hs]
  haveI hloc : IsLocalization.AtPrime (GaloisRep.ratLocalizedAt ℓ) s.asIdeal := by
    show IsLocalization s.asIdeal.primeCompl (GaloisRep.ratLocalizedAt ℓ)
    rw [hM]
    exact this
  set R : Type := ↥(GaloisRep.ratLocalizedAt ℓ)
  let L : Type := Localization.AtPrime s.asIdeal
  let K : Type := s.asIdeal.ResidueField
  let e : R ≃ₐ[ℤ] L := IsLocalization.algEquiv s.asIdeal.primeCompl R L
  let φ₀ : R →+* K := (IsLocalRing.residue L).comp e.toAlgHom.toRingHom
  let ι := Scheme.Spec.residueFieldIso (CommRingCat.of ℤ) s
  let φ : R →+* (Spec (CommRingCat.of ℤ)).residueField s := ι.inv.hom.comp φ₀
  refine ⟨φ, ?_, ?_, ?_⟩
  ·
    apply (ι.commRingCatIsoToRingEquiv.symm.surjective).comp
    exact (IsLocalRing.residue_surjective).comp e.surjective
  ·
    show ι.inv.hom (IsLocalRing.residue L (e (ℓ : R))) = 0
    have he : e (ℓ : R) = algebraMap ℤ L (ℓ : ℤ) := by
      rw [show (ℓ : R) = algebraMap ℤ R (ℓ : ℤ) from (map_natCast (algebraMap ℤ R) ℓ).symm,
        AlgEquiv.commutes]
    rw [he, (IsLocalRing.residue_eq_zero_iff _).mpr, map_zero]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff L s.asIdeal (ℓ : ℤ)).mpr
    rw [hs]
    exact Ideal.mem_span_singleton_self _
  ·
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcomp : φ.comp (algebraMap ℤ R) = ι.inv.hom.comp (algebraMap ℤ K) := RingHom.ext_int _ _
    rw [hcomp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp]
    exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of ℤ) s
