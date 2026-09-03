import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedOrbitalIntegralOn_comp_scalar_mul_iff
    (K L A : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ)
    (h : AutomorphicForm.twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      AutomorphicForm.twistedCentralizer K L A σ δ) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ'
        (fun g => φ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)) I ↔
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)
        (@Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
          (fun t => ⟨(t : GL (Fin 2) (L ⊗[K] A)), h.symm ▸ t.2⟩) τ')
        φ I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff.solution
