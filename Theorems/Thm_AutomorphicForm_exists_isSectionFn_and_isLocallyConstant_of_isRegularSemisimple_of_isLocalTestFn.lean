import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

theorem AutomorphicForm.exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    [@Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ]
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ,
      AutomorphicForm.IsSectionFn K v γ τ fv w ∧ IsLocallyConstant w := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isSectionFn_and_isLocallyConstant_of_isRegularSemisimple_of_isLocalTestFn.solution
