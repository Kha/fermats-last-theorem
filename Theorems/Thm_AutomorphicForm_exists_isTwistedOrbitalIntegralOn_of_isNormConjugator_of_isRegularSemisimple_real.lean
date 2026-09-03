import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
    (γ : GL (Fin 2) ℝ) (hγ : IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] ℝ)) (hy : IsNormConjugator K L ℝ σ γ δ y)
    (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_real.solution
