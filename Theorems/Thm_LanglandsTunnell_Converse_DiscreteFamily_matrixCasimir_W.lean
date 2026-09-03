import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchCasimir

theorem LanglandsTunnell.Converse.DiscreteFamily.matrixCasimir_W (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀)
    (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) :
    matrixCasimir (DiscreteFamily.W u₀ k₀) x =
      (RealArchParam.discrete u₀ k₀ hk).laplaceEigenvalue * DiscreteFamily.W u₀ k₀ x := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_matrixCasimir_W.solution
