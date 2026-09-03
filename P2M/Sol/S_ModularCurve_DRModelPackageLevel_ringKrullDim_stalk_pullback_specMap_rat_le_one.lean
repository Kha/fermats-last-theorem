import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import P2M.Util
namespace P2MW.S_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_pullback_specMap_rat_le_one

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (y : ↥(pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))) :
    ringKrullDim ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) ≤ 1 := by

  haveI hsm : SmoothOfRelativeDimension 1
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := 𝔓.smooth_generic
  haveI hgi : GeometricallyIntegral
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := 𝔓.geomIntegral_generic
  haveI hS : Smooth (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) :=
    SmoothOfRelativeDimension.smooth 1 _
  haveI : Flat (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := inferInstance
  haveI : LocallyOfFinitePresentation (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) :=
    inferInstance
  haveI : UniversallyOpen (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) :=
    UniversallyOpen.of_flat _
  haveI : IsIntegral (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))

  haveI hval : ValuationRing ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) y

  haveI : LocallyOfFinitePresentation (toBase N₀ p) := 𝔓.lfp
  haveI : LocallyOfFiniteType (toBase N₀ p) := inferInstance
  haveI : IsLocallyNoetherian (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))) := inferInstance
  haveI : IsNoetherianRing ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) := inferInstance

  haveI : IsPrincipalIdealRing ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) :=
    (isPrincipalIdealRing_iff _).mpr fun I => IsBezout.isPrincipal_of_FG I (IsNoetherian.noetherian I)
  have hdim : Ring.KrullDimLE 1 ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) := IsPrincipalIdealRing.krullDimLE_one _
  have h := hdim.krullDim_le
  simpa [ringKrullDim] using h
