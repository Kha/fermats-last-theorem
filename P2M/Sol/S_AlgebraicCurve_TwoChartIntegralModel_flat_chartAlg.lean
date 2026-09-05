import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg

set_option autoImplicit false

universe u

theorem solution
    {R F : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field F] [Algebra R F]
    (hRF : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) := by
  have hinj : Function.Injective (algebraMap R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)) :=
    fun a b hab => hRF (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

