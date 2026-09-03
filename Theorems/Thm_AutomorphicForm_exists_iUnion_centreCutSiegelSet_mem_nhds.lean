import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped Topology

theorem AutomorphicForm.exists_iUnion_centreCutSiegelSet_mem_nhds (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds.solution
