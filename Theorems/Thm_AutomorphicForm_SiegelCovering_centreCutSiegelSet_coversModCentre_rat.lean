import Definitions.Def_AutomorphicForm_SiegelCovering
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat
attribute [-simp] AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe

theorem AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat.solution
