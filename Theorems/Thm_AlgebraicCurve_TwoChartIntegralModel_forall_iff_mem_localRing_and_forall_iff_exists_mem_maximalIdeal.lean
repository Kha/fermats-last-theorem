import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [IsIntegral (AlgebraicCurve.TwoChartIntegralModel R F j)]
    (φ : F ≃+* (AlgebraicCurve.TwoChartIntegralModel R F j).functionField)
    (hφFin : ∀ (y : ↥(XFin R F j)) (b : ↥(chartAlgFin R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιFin R F j) ''ᵁ ⊤) ((ιFin R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιFin R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv.hom b))))
    (hφInf : ∀ (y : ↥(XInf R F j)) (b : ↥(chartAlgInf R F j)),
        φ (b : F) = algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιInf R F j).base y)) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField
          (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ((ιInf R F j) ''ᵁ ⊤) ((ιInf R F j).base y) ⟨y, trivial, rfl⟩).hom
            (((ιInf R F j).appIso ⊤).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf R F j))).inv.hom b))))
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) (f : F) :
    (((∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
          ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
       (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
          ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ f * (h : F) = (g : F))) ↔
      f ∈ SemistableModel.localRing (AlgebraicCurve.TwoChartIntegralModel R F j) φ x) ∧
    (((∀ y : ↥(XFin R F j), (ιFin R F j).base y = x →
          ∃ g h : ↥(chartAlgFin R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F)) ∧
       (∀ y : ↥(XInf R F j), (ιInf R F j).base y = x →
          ∃ g h : ↥(chartAlgInf R F j), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : F) = (g : F))) ↔
      ∃ s ∈ maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x),
        f = φ.symm (algebraMap ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) (AlgebraicCurve.TwoChartIntegralModel R F j).functionField s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_forall_iff_mem_localRing_and_forall_iff_exists_mem_maximalIdeal.solution
