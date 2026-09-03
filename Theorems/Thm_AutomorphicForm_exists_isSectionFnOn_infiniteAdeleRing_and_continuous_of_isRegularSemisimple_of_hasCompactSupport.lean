import Definitions.Def_AutomorphicForm_TwistedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport

set_option autoImplicit false

open NumberField MeasureTheory

theorem AutomorphicForm.exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K]
    (γ : GL (Fin 2) (InfiniteAdeleRing K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ]
    (f : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hf : HasCompactSupport f) :
    ∃ w : GL (Fin 2) (InfiniteAdeleRing K) → ℝ,
      AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K) γ τ f w ∧ Continuous w := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSectionFnOn_infiniteAdeleRing_and_continuous_of_isRegularSemisimple_of_hasCompactSupport.solution
