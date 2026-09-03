import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed

set_option autoImplicit false

open AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.eq_chartAlgFin_of_isIntegral_of_integrallyClosed
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (B : Subalgebra R F) (hj : j ∈ B)
    (hint : ∀ x ∈ B, IsIntegral (Algebra.adjoin R ({j} : Set F)) x)
    (hic : ∀ x : F, IsIntegral B x → x ∈ B) :
    B = chartAlgFin R F j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_eq_chartAlgFin_of_isIntegral_of_integrallyClosed.solution
