import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import P2M.Util
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_germ_iotaFin_algebraMap_eq_germ_top_toBase_appTop

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (y : ↥(XFin R F j)) (hy : (ιFin R F j).base y = z) (r : R) :
    ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom
        (((ιFin R F j).appIso ⊤).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom (algebraMap R ↥(chartAlgFin R F j) r))) =
      ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ z trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  subst hy
  obtain ⟨e, h1, h2⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin R F j y ⟨y, trivial, rfl⟩
  have hinj : Function.Injective e.hom.hom := by
    intro a b hab
    have := congrArg e.inv.hom hab
    simpa [← CommRingCat.comp_apply, e.hom_inv_id] using this
  apply hinj
  rw [h2 (algebraMap R _ r), h1 r]
  exact (IsScalarTower.algebraMap_apply R ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal) r).symm
