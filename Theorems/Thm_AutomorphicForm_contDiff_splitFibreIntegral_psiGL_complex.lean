import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.contDiff_splitFibreIntegral_psiGL_complex
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
    (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℂ σ ι hdeg hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport φ) :
    (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, splitFibreIntegral K L hdeg σ hσ ℂ ι μA φ g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
    HasCompactSupport (splitFibreIntegral K L hdeg σ hσ ℂ ι μA φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex.solution
