import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_one_forall_exists_isHaarMeasure_coupled_toTensorGL_mul_scalar_one
attribute [-simp] LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_one_forall_exists_isHaarMeasure_coupled_toTensorGL_mul_scalar_one
    (d : ℝˣ) :
    ∃ U ∈ nhds (1 : GL (Fin 2) ℝ), ∀ t ∈ U, (t = 1 ∨ IsRegularSemisimple t) →
      ((twistedCentralizer ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)) : Set (GL (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
        toTensorGL ℝ ℂ ℝ '' (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) ∧
      ∀ (τ : @Measure (Subgroup.centralizer ({t} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ t)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ t) τ →
        ∃ τ' : @Measure
            (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))),
          @Measure.IsHaarMeasure _ _ _
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
              (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ' ∧
          Coupled ℝ ℂ ℝ Complex.conjAe t (toTensorGL ℝ ℂ ℝ (t * Matrix.GeneralLinearGroup.scalar (Fin 2) d))
            1 τ τ' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_one_forall_exists_isHaarMeasure_coupled_toTensorGL_mul_scalar_one.solution
