import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_DiscreteFamily_exists_W_ne_zero

set_option autoImplicit false

open LanglandsTunnell.Converse.DiscreteFamily

theorem LanglandsTunnell.Converse.DiscreteFamily.exists_W_ne_zero (u₀ : ℂ) (k₀ : ℕ) :
    ∃ g : GL (Fin 2) ℝ, W u₀ k₀ (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_exists_W_ne_zero.solution
