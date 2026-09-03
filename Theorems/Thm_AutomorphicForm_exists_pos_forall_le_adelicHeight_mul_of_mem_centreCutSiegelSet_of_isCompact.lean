import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_NumberField_AdelicHeight
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact

set_option autoImplicit false

open NumberField AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (T : Set (AdelicGL2 (𝓞 F) F)) (hT : IsCompact T) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ g ∈ centreCutSiegelSet F c u d₁ d₂, ∀ y ∈ T,
      h₀ ≤ NumberField.AdelicHeight.adelicHeight F (g * y) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_pos_forall_le_adelicHeight_mul_of_mem_centreCutSiegelSet_of_isCompact.solution
