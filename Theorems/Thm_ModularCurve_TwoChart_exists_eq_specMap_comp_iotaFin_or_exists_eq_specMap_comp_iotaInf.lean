import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import P2M.Util
import P2M.Sol.S_ModularCurve_TwoChart_exists_eq_specMap_comp_iotaFin_or_exists_eq_specMap_comp_iotaInf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem ModularCurve.TwoChart.exists_eq_specMap_comp_iotaFin_or_exists_eq_specMap_comp_iotaInf
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (g : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel A K j) :
    (∃ β : ↥(ModularCurve.TwoChart.chartAlgFin A K j) →+* O,
        g = Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.TwoChart.ιFin A K j) ∨
      (∃ β : ↥(ModularCurve.TwoChart.chartAlgInf A K j) →+* O,
        g = Spec.map (CommRingCat.ofHom β) ≫ ModularCurve.TwoChart.ιInf A K j) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TwoChart_exists_eq_specMap_comp_iotaFin_or_exists_eq_specMap_comp_iotaInf.solution
