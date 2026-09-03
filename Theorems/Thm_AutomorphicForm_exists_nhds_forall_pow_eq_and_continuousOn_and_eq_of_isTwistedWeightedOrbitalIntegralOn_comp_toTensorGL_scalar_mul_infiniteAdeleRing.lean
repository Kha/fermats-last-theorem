import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) μ)
    (wt : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 0 = 0 → wt (t * x) = wt x)
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (hγ₀₁ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hγ₁₀ : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ δ = AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) γ)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)) (hτ' : τ'.IsHaarMeasure)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ W ∈ nhds (1 : InfiniteAdeleRing K), ∃ ρ : InfiniteAdeleRing K → (InfiniteAdeleRing K)ˣ, ∃ g : InfiniteAdeleRing K → ℂ,
      ((ρ 1 : InfiniteAdeleRing K) = 1) ∧
      (∀ ε ∈ W, ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ^ Module.finrank K L = ε) ∧
      ContinuousOn (fun ε => ((ρ ε : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) W ∧
      ContinuousOn g W ∧
      ∀ ε ∈ W, ∀ J : ℂ,
        AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ μ wt δ τ'
          (fun y => φ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (ρ ε)) * y)) J →
        J = g ε := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_nhds_forall_pow_eq_and_continuousOn_and_eq_of_isTwistedWeightedOrbitalIntegralOn_comp_toTensorGL_scalar_mul_infiniteAdeleRing.solution
