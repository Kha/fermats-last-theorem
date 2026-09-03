import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import P2M.Util
import P2M.Sol.S_ModularCurve_TwoChart_exists_eq_spec_map_comp_iotaFin_of_apply_closedPoint_mem_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem ModularCurve.TwoChart.exists_eq_spec_map_comp_iotaFin_of_apply_closedPoint_mem_range
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
    (O : Type u) [CommRing O] [IsLocalRing O]
    (ξ : Spec (CommRingCat.of O) ⟶ ModularCurve.TwoChartModel A K j)
    (hξ : ξ.base (IsLocalRing.closedPoint O) ∈ Set.range (ModularCurve.TwoChart.ιFin A K j).base) :
    ∃ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A K j) →+* O,
      ξ = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A K j := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_TwoChart_exists_eq_spec_map_comp_iotaFin_of_apply_closedPoint_mem_range.solution
