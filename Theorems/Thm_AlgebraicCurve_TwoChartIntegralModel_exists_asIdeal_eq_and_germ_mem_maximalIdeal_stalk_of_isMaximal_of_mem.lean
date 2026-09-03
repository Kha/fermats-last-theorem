import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_asIdeal_eq_and_germ_mem_maximalIdeal_stalk_of_isMaximal_of_mem

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel~exists_stalk_iso_localization_chartAlgFin"

theorem AlgebraicCurve.TwoChartIntegralModel.exists_asIdeal_eq_and_germ_mem_maximalIdeal_stalk_of_isMaximal_of_mem
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : Ideal ↥(chartAlgFin R F j)) (hy : y.IsMaximal)
    (r : R) (hr : algebraMap R ↥(chartAlgFin R F j) r ∈ y) :
    ∃ (y' : ↥(XFin R F j)), y'.asIdeal = y ∧
      (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y') trivial).hom
          (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) ∈
        IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y')) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_asIdeal_eq_and_germ_mem_maximalIdeal_stalk_of_isMaximal_of_mem.solution
