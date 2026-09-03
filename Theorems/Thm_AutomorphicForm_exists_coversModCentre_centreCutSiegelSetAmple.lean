import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_SiegelCovering
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧
      ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)),
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) →
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c (max u R) d₁ d₂ κ) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple.solution
