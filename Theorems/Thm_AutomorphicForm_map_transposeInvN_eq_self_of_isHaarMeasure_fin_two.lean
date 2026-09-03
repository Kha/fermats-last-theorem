import Mathlib
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import P2M.Util
import P2M.Sol.S_AutomorphicForm_map_transposeInvN_eq_self_of_isHaarMeasure_fin_two

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal

theorem AutomorphicForm.map_transposeInvN_eq_self_of_isHaarMeasure_fin_two
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μ₂ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      Measure.map (fun h : GL (Fin 2) (v.adicCompletion ℚ) => transposeInvN (Fin 2) h) μ₂ = μ₂ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_map_transposeInvN_eq_self_of_isHaarMeasure_fin_two.solution
