import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] AutomorphicForm.centralizerBorel

theorem AutomorphicForm.eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) [τ.IsHaarMeasure]
    (c : ℝ) (hc : 0 < c)
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : AutomorphicForm.IsArchTestFactor K f)
    (I I' : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν γ τ f I)
    (hI' : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν γ (ENNReal.ofReal c • τ) f I') :
    I' = (c : ℂ)⁻¹ * I := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_eq_inv_mul_of_isOrbitalIntegralOn_of_isOrbitalIntegralOn_smul_infiniteAdeleRing.solution
