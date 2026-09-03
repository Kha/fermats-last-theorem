import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import P2M.Util
namespace P2MW.S_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem solution (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] (κ : Type) [CommRing κ] [CharP κ p] (toκ : O →+* κ)
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))) :
    (DRModel.baseChangeMap toκ).base y ∉
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  intro h
  have hcomm : DRModel.baseChangeMap toκ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) :=
    pullback.lift_snd _ _ _
  have h' : (DRModel.baseChangeMap toκ ≫ pullback.snd (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base y ∈
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := h
  rw [hcomm] at h'
  change PrimeSpectrum.comap toκ ((pullback.snd (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base y) ∈ PrimeSpectrum.basicOpen ((p : ℕ) : O) at h'
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast,
    CharP.cast_eq_zero] at h'
  exact h' (Ideal.zero_mem _)
