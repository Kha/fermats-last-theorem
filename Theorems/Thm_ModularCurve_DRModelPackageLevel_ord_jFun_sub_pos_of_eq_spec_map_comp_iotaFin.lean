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
import P2M.Sol.S_ModularCurve_DRModelPackageLevel_ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel
  ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem ModularCurve.DRModelPackageLevel.ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (f : Spec (CommRingCat.of ↥A) ⟶ X N₀ p)
    (hu : barPt A ≫ f = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
    (φ : ↥(chartAlgFin (N₀ * p) p) →+* ↥A) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p) :
    0 < (𝔓.Meta.pointEquivPlace y).ord
      (ProlongationTuple.jFun N₀ p -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))
          ((φ (jChartFin (N₀ * p) p) : ↥A) : AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_DRModelPackageLevel_ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin.solution
