import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_of_map_le_of_aeval_mem

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.isMaximal_of_map_le_of_aeval_mem
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (𝔪 : Ideal R) [𝔪.IsMaximal]
    (y : ↥(XFin R F j))
    (hy : Ideal.map (algebraMap R ↥(chartAlgFin R F j)) 𝔪 ≤ y.asIdeal)
    (halg : ∃ P : Polynomial R, P.map (Ideal.Quotient.mk 𝔪) ≠ 0 ∧
      (Polynomial.aeval (jChartFin R F j) P : ↥(chartAlgFin R F j)) ∈ y.asIdeal) :
    y.asIdeal.IsMaximal ∧
      (Algebra.FiniteType R ↥(chartAlgFin R F j) → Module.Finite R (↥(chartAlgFin R F j) ⧸ y.asIdeal)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isMaximal_of_map_le_of_aeval_mem.solution
