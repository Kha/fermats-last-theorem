import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import P2M.Util
namespace P2MW.S_ModularCurve_DRLevel_bcMap_apply_notMem_preimage_basicOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (O : Type) [CommRing O] (ρO : DRLevel.R q →+* O) (κ : Type) [CommRing κ] [CharP κ q] (toκ : O →+* κ)
    (y : ↥(DRLevel.fibre (N₀ := N₀) (toκ.comp ρO))) :
    (DRLevel.bcMap ρO toκ).base y ∉ (DRLevel.XO.toBase (N₀ := N₀) ρO) ⁻¹ᵁ (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := by
  intro h
  have hcomm : DRLevel.bcMap ρO toκ ≫ DRLevel.XO.toBase (N₀ := N₀) ρO = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ) :=
    pullback.lift_snd _ _ _
  have h' : (DRLevel.bcMap ρO toκ ≫ DRLevel.XO.toBase (N₀ := N₀) ρO).base y ∈
      (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := h
  rw [hcomm] at h'
  change PrimeSpectrum.comap toκ ((pullback.snd (DRLevel.toBase N₀ q)
      (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))).base y) ∈ PrimeSpectrum.basicOpen ((q : ℕ) : O) at h'
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_natCast,
    CharP.cast_eq_zero] at h'
  exact h' (Ideal.zero_mem _)
