import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin R F j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).base y = z) :
    ∃ e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z ≅
        CommRingCat.of (Localization.AtPrime y.asIdeal),
      (∀ r : R, e.hom.hom
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ
                ((AlgebraicCurve.TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
              ((((AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv.hom).comp
                (Scheme.ΓSpecIso (CommRingCat.of
                  ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))).inv.hom)) a) =
        algebraMap (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j))
          (Localization.AtPrime y.asIdeal) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq.solution
