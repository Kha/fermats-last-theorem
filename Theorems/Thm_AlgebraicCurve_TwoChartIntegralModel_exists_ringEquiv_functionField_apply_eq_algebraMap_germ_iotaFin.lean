import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaFin

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel~exists_stalk_iso_localization_chartAlgFin"

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaFin
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (hfrac : IsFractionRing ↥(chartAlgFin R F j) F) :
    ∃ φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField,
      (∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b)))) ∧
      (∀ r : R, φ (algebraMap R F r) = SemistableModel.baseToFunctionField (toBase R F j) r) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_ringEquiv_functionField_apply_eq_algebraMap_germ_iotaFin.solution
