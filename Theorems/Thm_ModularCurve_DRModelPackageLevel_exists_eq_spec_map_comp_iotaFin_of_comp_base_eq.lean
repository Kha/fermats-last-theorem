import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction
import P2M.Util
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] [IsLocalRing A] (red : A →+* κ)
    (hker : ∀ c : A, c ∈ IsLocalRing.maximalIdeal A → red c = 0)
    (f : Spec (CommRingCat.of A) ⟶ X N₀ p)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ f)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)))
    (hn : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      uκ.base (IsLocalRing.closedPoint κ)) :
    ∃ φ : ↥(chartAlgFin (N₀ * p) p) →+* A, f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq.solution
