import Definitions.Def_LanglandsTunnell_Converse_ExplicitWhittakerFunctions
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_DiscreteFamily_exists_archDatumR_W_eq

set_option autoImplicit false

open LanglandsTunnell.Converse LanglandsTunnell.Converse.DiscreteFamily

theorem LanglandsTunnell.Converse.DiscreteFamily.exists_archDatumR_W_eq (u₀ : ℂ) (k₀ : ℕ) (hk : 1 ≤ k₀) :
    ∃ D : ArchDatumR (RealArchParam.discrete u₀ k₀ hk), D.W = W u₀ k₀ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_DiscreteFamily_exists_archDatumR_W_eq.solution
