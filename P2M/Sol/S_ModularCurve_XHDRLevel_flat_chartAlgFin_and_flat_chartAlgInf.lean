import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import P2M.Util
namespace P2MW.S_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_XHDRLevel_flat_chartAlgFin_and_flat_chartAlgInf.AlgebraicCurve ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlg chartAlgFin chartAlgInf"
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

universe u

theorem flat_chartAlg {R F : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field F]
    [Algebra R F] (hRF : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R ↥(chartAlg R F S) := by
  have hinj : Function.Injective (algebraMap R ↥(chartAlg R F S)) :=
    fun a b hab => hRF (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree R ↥(chartAlg R F S) := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

end AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    Module.Flat (R p) ↥(chartAlgFin p Γ hj) ∧ Module.Flat (R p) ↥(chartAlgInf p Γ hj) := by
  haveI : IsPrincipalIdealRing (R p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p

  have hRF : Function.Injective (algebraMap (R p) ↥(qExpFunctionFieldC ℚ Γ)) :=
    (algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ)).injective.comp Subtype.val_injective
  exact ⟨TwoChartIntegralModel.flat_chartAlg hRF _, TwoChartIntegralModel.flat_chartAlg hRF _⟩

