import Mathlib
import P2M.Util
namespace P2MW.S_Algebra_IsSmoothAt_flat_localization_atPrime

set_option autoImplicit false

open Algebra

theorem solution (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    Module.Flat R (Localization.AtPrime p) := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R p
  haveI := hsm
  haveI : Module.Flat R (Localization.Away f) := Algebra.Smooth.flat R _
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro x ⟨n, rfl⟩
    exact fun h => hf (‹p.IsPrime›.mem_of_pow_mem n h)
  letI : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f) p.primeCompl hle
  haveI : IsScalarTower A (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  haveI : IsLocalization ((p.primeCompl).map (algebraMap A (Localization.Away f))) (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  haveI : Module.Flat (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) ((p.primeCompl).map (algebraMap A (Localization.Away f)))
  haveI : IsScalarTower R (Localization.Away f) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p) r,
        IsScalarTower.algebraMap_apply R A (Localization.Away f) r,
        ← IsScalarTower.algebraMap_apply A (Localization.Away f) (Localization.AtPrime p)])
  exact Module.Flat.trans R (Localization.Away f) (Localization.AtPrime p)
