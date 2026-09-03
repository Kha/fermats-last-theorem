import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (w : InfinitePlace L) (hw : w.IsRamified K) :
    ∃ (e : (w.comap (algebraMap K L)).Completion ≃+* ℝ)
      (E : L ⊗[K] (w.comap (algebraMap K L)).Completion ≃+* ℂ ⊗[ℝ] ℝ),
      Continuous e ∧ Continuous e.symm ∧ Continuous E ∧ Continuous E.symm ∧
      (∀ z, E (sigmaTensor K L (w.comap (algebraMap K L)).Completion σ z) =
        sigmaTensor ℝ ℂ ℝ Complex.conjAe (E z)) ∧
      (∀ g : GL (Fin 2) (w.comap (algebraMap K L)).Completion,
        Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L (w.comap (algebraMap K L)).Completion g) =
          toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.map e.toRingHom g)) ∧
      (∀ (x : L) (a : (w.comap (algebraMap K L)).Completion),
        (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
          (Algebra.TensorProduct.rid ℝ ℝ ℂ)) (E (x ⊗ₜ a)) = w.embedding x * (e a : ℂ)) ∧
      (∀ k : K, (e (algebraMap K (w.comap (algebraMap K L)).Completion k) : ℂ) = w.embedding (algebraMap K L k)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified.solution
