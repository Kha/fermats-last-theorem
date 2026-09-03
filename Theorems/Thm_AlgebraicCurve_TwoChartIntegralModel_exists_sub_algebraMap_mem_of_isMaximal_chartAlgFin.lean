import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

theorem AlgebraicCurve.TwoChartIntegralModel.exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin
    {R F : Type} [CommRing R] [IsLocalRing R] [Field F] [Algebra R F]
    (hres : IsAlgClosed (ResidueField R)) (j : F)
    (y : Ideal ↥(chartAlgFin R F j)) (hy : y.IsMaximal)
    (hmy : ∀ r ∈ maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) r ∈ y)
    (b : ↥(chartAlgFin R F j)) : ∃ c : R, b - algebraMap R ↥(chartAlgFin R F j) c ∈ y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_sub_algebraMap_mem_of_isMaximal_chartAlgFin.solution
