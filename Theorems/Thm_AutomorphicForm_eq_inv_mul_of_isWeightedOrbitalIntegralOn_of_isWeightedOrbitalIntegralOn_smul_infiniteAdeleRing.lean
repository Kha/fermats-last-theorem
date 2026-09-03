import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] AutomorphicForm.centralizerBorel

theorem AutomorphicForm.eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) [τ.IsHaarMeasure]
    (c : ℝ) (hc : 0 < c)
    (wt : GL (Fin 2) (InfiniteAdeleRing K) → ℝ) (hwtc : Continuous wt)
    (hwt : ∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))),
      ∀ x : GL (Fin 2) (InfiniteAdeleRing K), wt ((t : GL (Fin 2) (InfiniteAdeleRing K)) * x) = wt x)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : AutomorphicForm.IsArchTestFactor K f)
    (J J' : ℂ) (hJ : AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν wt γ τ f J)
    (hJ' : AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) ν wt γ (ENNReal.ofReal c • τ) f J') :
    J' = (c : ℂ)⁻¹ * J := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_inv_mul_of_isWeightedOrbitalIntegralOn_of_isWeightedOrbitalIntegralOn_smul_infiniteAdeleRing.solution
