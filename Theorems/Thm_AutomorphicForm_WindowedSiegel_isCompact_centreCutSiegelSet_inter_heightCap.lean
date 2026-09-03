import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import P2M.Util
import P2M.Sol.S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap

theorem AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap.solution
