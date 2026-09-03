import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.two_le_ringKrullDim_stalk_of_isMaximal_of_mem
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (F : Type u) [Field F] [Algebra A F] (j : F) [Fact (j ≠ 0)]
    (htj : Transcendental A j)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (y : ↥(XFin A F j)) (hymax : y.asIdeal.IsMaximal)
    (hyϖ : algebraMap A ↥(chartAlgFin A F j) ϖ ∈ y.asIdeal) :
    2 ≤ ringKrullDim ↑((AlgebraicCurve.TwoChartIntegralModel A F j).presheaf.stalk ((ιFin A F j).base y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_two_le_ringKrullDim_stalk_of_isMaximal_of_mem.solution
