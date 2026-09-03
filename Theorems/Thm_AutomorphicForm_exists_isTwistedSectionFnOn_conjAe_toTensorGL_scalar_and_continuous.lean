import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
    (d : ℝˣ) (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure
      (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ') :
    ∃ w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ' φ w ∧
        Continuous w := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous.solution
