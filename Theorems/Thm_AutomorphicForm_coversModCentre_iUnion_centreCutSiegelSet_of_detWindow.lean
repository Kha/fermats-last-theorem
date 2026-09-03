import Definitions.Def_AutomorphicForm_SiegelCovering
import P2M.Util
import P2M.Sol.S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering

theorem AutomorphicForm.coversModCentre_iUnion_centreCutSiegelSet_of_detWindow
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ e₁ e₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (he₂ : 0 < e₂) (he : e₁ ≤ e₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u e₁ e₂) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_coversModCentre_iUnion_centreCutSiegelSet_of_detWindow.solution
