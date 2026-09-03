import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K))
    (δ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (z : (L ⊗[K] v.adicCompletion K)ˣ)
    (hz : AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ (y₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (r : ENNReal),
      AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ y₀ ∧ r ≠ 0 ∧ r ≠ ⊤ ∧
        AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ y₀ τ (r • τ') := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isNormConjugator_and_coupled_smul_of_isSigmaConjugate_scalar_of_finrank_eq_two.solution
