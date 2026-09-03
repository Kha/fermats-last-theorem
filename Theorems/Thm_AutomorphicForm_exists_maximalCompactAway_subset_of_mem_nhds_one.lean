import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm Filter Topology

theorem AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one
    (F : Type) [Field F] [NumberField F]
    (W : Set (AdelicGL2 (𝓞 F) F)) (_hW : W ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      (maximalCompactAway F S₀ : Set (AdelicGL2 (𝓞 F) F)) ⊆ W := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_maximalCompactAway_subset_of_mem_nhds_one.solution
