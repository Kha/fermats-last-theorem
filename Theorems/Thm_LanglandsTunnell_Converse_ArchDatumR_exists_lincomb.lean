import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_exists_lincomb

set_option autoImplicit false

open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.exists_lincomb {P : RealArchParam} (D₁ D₂ : ArchDatumR P)
    (c₁ c₂ : ℂ) :
    ∃ D : ArchDatumR P, D.W = fun g => c₁ * D₁.W g + c₂ * D₂.W g := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_lincomb.solution
