import Definitions.Def_AutomorphicForm_SplitFibreIntegral
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
    (γ : GL (Fin 2) ℂ) (hγ : IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] ℂ)) (hy : IsNormConjugator K L ℂ σ γ δ y)
    (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_of_isNormConjugator_of_isRegularSemisimple_complex.solution
