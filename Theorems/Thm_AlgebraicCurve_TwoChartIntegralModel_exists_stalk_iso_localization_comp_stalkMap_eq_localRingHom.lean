import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (F₁ : Type u) [Field F₁] [Algebra R F₁] (j₁ : F₁) [Fact (j₁ ≠ 0)]
    (ιF : ↥(chartAlgFin R F₁ j₁) →ₐ[R] ↥(chartAlgFin R F j))
    (m : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F₁ j₁)
    (hmF : Spec.map (CommRingCat.ofHom ιF.toRingHom) ≫ ιFin R F₁ j₁ = ιFin R F j ≫ m)
    (y : ↥(XFin R F j)) :
    ∃ (e : (AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y) ≅
          CommRingCat.of (Localization.AtPrime y.asIdeal))
      (e₁ : (AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.stalk (m.base ((ιFin R F j).base y)) ≅
          CommRingCat.of (Localization.AtPrime (y.asIdeal.comap ιF.toRingHom))),
      (∀ r : R, e.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
            (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime y.asIdeal) r) ∧
      (∀ r : R, e₁.hom.hom
          ((((AlgebraicCurve.TwoChartIntegralModel R F₁ j₁).presheaf.germ ⊤ (m.base ((ιFin R F j).base y)) trivial).hom
            (((toBase R F₁ j₁).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))) =
        algebraMap R (Localization.AtPrime (y.asIdeal.comap ιF.toRingHom)) r) ∧
      e₁.hom ≫ CommRingCat.ofHom
          (Localization.localRingHom (y.asIdeal.comap ιF.toRingHom) y.asIdeal ιF.toRingHom rfl) =
        m.stalkMap ((ιFin R F j).base y) ≫ e.hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_comp_stalkMap_eq_localRingHom.solution
