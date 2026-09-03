import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv

set_option autoImplicit false

open AlgebraicCurve

universe u

theorem AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv
    {R : Type u} [CommRing R] {F F' : Type u} [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (e : F ≃+* F') (he : ∀ r : R, e (algebraMap R F r) = algebraMap R F' r) :
    (∀ (S : Set F) (x : F),
      x ∈ TwoChartIntegralModel.chartAlg R F S ↔ e x ∈ TwoChartIntegralModel.chartAlg R F' (e '' S)) ∧
    ∀ (j : F) [Fact (j ≠ 0)] [Fact (e j ≠ 0)],
      (∃ ε : ↥(TwoChartIntegralModel.chartAlgInf R F j) ≃+* ↥(TwoChartIntegralModel.chartAlgInf R F' (e j)),
        (∀ b, ((ε b : ↥(TwoChartIntegralModel.chartAlgInf R F' (e j))) : F') = e (b : F)) ∧
        ∀ r : R, ε (algebraMap R _ r) = algebraMap R _ r) ∧
      (∃ ε : ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃+* ↥(TwoChartIntegralModel.chartAlgFin R F' (e j)),
        (∀ b, ((ε b : ↥(TwoChartIntegralModel.chartAlgFin R F' (e j))) : F') = e (b : F)) ∧
        ∀ r : R, ε (algebraMap R _ r) = algebraMap R _ r) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_iff_mem_chartAlg_image_of_ringEquiv.solution
