import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_of_coupled
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsOpenPosMeasure _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (hc : AutomorphicForm.Coupled K L A σ γ δ y τ τ') :
    ∃ d : (L ⊗[K] A)ˣ, AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled.solution
