import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.DiscreteFamily.W_archWeightChar (u₀ : ℂ) (k₀ : ℕ) :
    ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      W u₀ k₀ ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ ((k₀ : ℤ) + 1) r : ℂ) * W u₀ k₀ (x : Matrix (Fin 2) (Fin 2) ℝ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_W_archWeightChar.solution
