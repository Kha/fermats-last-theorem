import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist

set_option autoImplicit false

open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.exists_sgnTwist (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2)
    (D : ArchDatumR (RealArchParam.principal u₁ a₁ u₂ a₂)) :
    ∃ D' : ArchDatumR (RealArchParam.principal u₁ (a₁ + 1) u₂ (a₂ + 1)),
      D'.W = fun g => ((SignType.sign g.det : ℝ) : ℂ) * D.W g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_sgnTwist.solution
