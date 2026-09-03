import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul
attribute [-instance] HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions
attribute [-simp] HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem AutomorphicForm.setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (μ : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))
    (hμ : @Measure.IsMulLeftInvariant (GL (Fin 2) (v.adicCompletion K))
      (AutomorphicForm.localGLBorel K v) _ μ)
    (s : ℝ) :
    ∫⁻ g in {g : GL (Fin 2) (v.adicCompletion K) |
        ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K},
        ((‖((Matrix.GeneralLinearGroup.det g : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖₊ : ℝ≥0∞) ^ s) ∂μ =
      μ (AutomorphicForm.localIntegralSet K v) *
        ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-s))⁻¹ *
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - s))⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_setLIntegral_nnnorm_det_rpow_setOf_integral_eq_measure_localIntegralSet_mul.solution
