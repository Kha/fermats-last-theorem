import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ) :
    ∃ β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ,
      Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β ∧
      (∀ x, 0 ≤ β x) ∧ (∃ C : ℝ, ∀ x, β x ≤ C) ∧
      ∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ t : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (t : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_measurable_forall_integral_localCentralizer_toTensorGL_mul_eq_one_of_diagonal.solution
