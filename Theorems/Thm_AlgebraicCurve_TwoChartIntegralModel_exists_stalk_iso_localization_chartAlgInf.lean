import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgInf
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XInf R F j))
    (hz : (ιInf R F j).base y ∈ (ιInf R F j) ''ᵁ ⊤) :
    ∃ e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y) ≅
        CommRingCat.of (Localization.AtPrime y.asIdeal),
      (∀ r : R, e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιInf R F j).base y) trivial).hom
            (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ a : ↥(chartAlgInf R F j), e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) hz).hom
            ((((ιInf R F j).appIso ⊤).inv).hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom a)))) =
        algebraMap ↥(chartAlgInf R F j) (Localization.AtPrime y.asIdeal) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgInf.solution
