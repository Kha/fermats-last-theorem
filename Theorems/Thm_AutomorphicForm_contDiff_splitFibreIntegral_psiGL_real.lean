import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_real

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.contDiff_splitFibreIntegral_psiGL_real
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℝ σ ι hdeg hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport φ) :
    (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    HasCompactSupport (splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_real.solution
