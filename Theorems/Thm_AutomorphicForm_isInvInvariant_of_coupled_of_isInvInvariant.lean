import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isInvInvariant_of_coupled_of_isInvInvariant

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isInvInvariant_of_coupled_of_isInvInvariant
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hc : AutomorphicForm.Coupled K L A σ γ δ y τ τ')
    (hτ : @Measure.IsInvInvariant _ (AutomorphicForm.centralizerBorel A γ) _ τ) :
    @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) _ τ' := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isInvInvariant_of_coupled_of_isInvInvariant.solution
