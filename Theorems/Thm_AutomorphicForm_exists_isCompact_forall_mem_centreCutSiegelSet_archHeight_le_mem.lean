import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem

set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicCentre
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem
    (F : Type) [Field F] [NumberField F] {c u d₁ d₂ : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) (Hcap : ℝ) :
    ∃ K₀ : Set (AdelicGL2 (𝓞 F) F), IsCompact K₀ ∧
      ∀ s ∈ centreCutSiegelSet F c u d₁ d₂, archHeight F (glArch (𝓞 F) F s) ≤ Hcap → s ∈ K₀ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isCompact_forall_mem_centreCutSiegelSet_archHeight_le_mem.solution
