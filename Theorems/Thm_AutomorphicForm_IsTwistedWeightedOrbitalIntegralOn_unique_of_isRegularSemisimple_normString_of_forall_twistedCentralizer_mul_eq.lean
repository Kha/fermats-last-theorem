import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import P2M.Util
import P2M.Sol.S_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μ)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (wt : GL (Fin 2) (L ⊗[K] A) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : AutomorphicForm.twistedCentralizer K L A σ δ, ∀ x : GL (Fin 2) (L ⊗[K] A),
      wt ((t : GL (Fin 2) (L ⊗[K] A)) * x) = wt x)
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] A)] φ)
    (hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C)
    {J'₁ J'₂ : ℂ} (h₁ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' φ J'₁)
    (h₂ : AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L A σ μ wt δ τ' φ J'₂) : J'₁ = J'₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_IsTwistedWeightedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString_of_forall_twistedCentralizer_mul_eq.solution
