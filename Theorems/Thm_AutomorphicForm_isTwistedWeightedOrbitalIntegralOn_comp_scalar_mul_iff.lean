import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_isTwistedWeightedOrbitalIntegralOn_comp_scalar_mul_iff

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedWeightedOrbitalIntegralOn_comp_scalar_mul_iff
    (K L A : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ)
    (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (J : ℂ)
    (h : AutomorphicForm.twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      AutomorphicForm.twistedCentralizer K L A σ δ) :
    AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ'
        (fun g => φ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)) J ↔
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)
        (@Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
          (fun t => ⟨(t : GL (Fin 2) (L ⊗[K] A)), h.symm ▸ t.2⟩) τ')
        φ J := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_isTwistedWeightedOrbitalIntegralOn_comp_scalar_mul_iff.solution
