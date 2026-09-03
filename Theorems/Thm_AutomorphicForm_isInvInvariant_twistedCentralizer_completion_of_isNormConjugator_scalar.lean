import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K) (c : (v.Completion)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : AutomorphicForm.IsNormConjugator K L v.Completion σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L v.Completion σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ) τ') :
    @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L v.Completion σ δ) _ τ' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar.solution
