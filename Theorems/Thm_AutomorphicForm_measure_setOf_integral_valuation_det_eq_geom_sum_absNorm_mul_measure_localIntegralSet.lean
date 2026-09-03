import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (μ : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hμ : @Measure.IsMulLeftInvariant (GL (Fin 2) (v.adicCompletion K))
      (AutomorphicForm.localGLBorel K v) _ μ)
    (k : ℕ) :
    μ {g : GL (Fin 2) (v.adicCompletion K) |
        (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
          Valued.v ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            WithZero.exp (-(k : ℤ))} =
      (∑ i ∈ Finset.range (k + 1), ((Ideal.absNorm v.asIdeal : ℕ) : ENNReal) ^ i) *
        μ (AutomorphicForm.localIntegralSet K v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_measure_setOf_integral_valuation_det_eq_geom_sum_absNorm_mul_measure_localIntegralSet.solution
