import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf.AlgebraicCurve TopologicalSpace"

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel.jChartFin TwoChartIntegralModel.jInvChartInf TwoChartIntegralModel TwoChartIntegralModel.ιFin TwoChartIntegralModel.ιInf"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "chartAlgFin chartAlgInf jChartFin jInvChartInf ιFin ιInf TwoChartsAux.U TwoChartsAux.V TwoChartsAux.f TwoChartsAux.g TwoChartsAux.res_f_mul_res_g"
namespace JJInvAux
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

theorem genericPoint_mem {Y : Scheme.{u}} [IsIntegral Y] (W : Y.Opens) [h : Nonempty (Scheme.Opens.toScheme W)] :
    genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by simpa using h)

theorem germToFunctionField_eq_germ {Y : Scheme.{u}} [IsIntegral Y] (W : Y.Opens) [Nonempty (Scheme.Opens.toScheme W)]
    (hη : genericPoint Y ∈ W) (s : Γ(Y, W)) :
    Y.germToFunctionField W s = (Y.presheaf.germ W (genericPoint Y) hη).hom s := rfl

end AlgebraicCurve.TwoChartIntegralModel.JJInvAux

open _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_germToFunctionField_jChartFin_mul_germToFunctionField_jInvChartInf.AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
    [hU : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))]
    [hV : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)))] :
    Y.germToFunctionField (f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
        (((f.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv
              (TwoChartIntegralModel.jChartFin R F j))))) *
      Y.germToFunctionField (f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤))
        (((f.app ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιInf R F j).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf R F j))).inv
              (TwoChartIntegralModel.jInvChartInf R F j))))) = 1 := by

  have hηU : genericPoint Y ∈ f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) := JJInvAux.genericPoint_mem _
  have hηV : genericPoint Y ∈ f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤) := JJInvAux.genericPoint_mem _
  have hηW : genericPoint Y ∈ f ⁻¹ᵁ (TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j) := ⟨hηU, hηV⟩
  rw [JJInvAux.germToFunctionField_eq_germ _ hηU, JJInvAux.germToFunctionField_eq_germ _ hηV]

  have iU : f ⁻¹ᵁ (TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j) ≤ f ⁻¹ᵁ ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) :=
    fun y hy => hy.1
  have iV : f ⁻¹ᵁ (TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j) ≤ f ⁻¹ᵁ ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤) :=
    fun y hy => hy.2
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE iU) (genericPoint Y) hηW,
    ← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE iV) (genericPoint Y) hηW]

  have nU : (Y.presheaf.map (homOfLE iU).op).hom (((f.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom
        (TwoChartsAux.f R F j))) =
      (f.app (TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j)).hom
        (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map (homOfLE inf_le_left).op).hom (TwoChartsAux.f R F j)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have nV : (Y.presheaf.map (homOfLE iV).op).hom (((f.app ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)).hom
        (TwoChartsAux.g R F j))) =
      (f.app (TwoChartsAux.U R F j ⊓ TwoChartsAux.V R F j)).hom
        (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.map (homOfLE inf_le_right).op).hom (TwoChartsAux.g R F j)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  change (Y.presheaf.germ _ (genericPoint Y) hηW).hom ((Y.presheaf.map (homOfLE iU).op).hom
      (((f.app ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom (TwoChartsAux.f R F j)))) *
    (Y.presheaf.germ _ (genericPoint Y) hηW).hom ((Y.presheaf.map (homOfLE iV).op).hom
      (((f.app ((TwoChartIntegralModel.ιInf R F j) ''ᵁ ⊤)).hom (TwoChartsAux.g R F j)))) = 1
  rw [nU, nV, ← map_mul, ← map_mul, TwoChartsAux.res_f_mul_res_g, map_one, map_one]
