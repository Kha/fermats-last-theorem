import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_exists_archDatumR_W_ne_zero
attribute [-simp] LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply

set_option autoImplicit false
open LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_archDatumR_W_ne_zero (P : RealArchParam) :
    ∃ D : ArchDatumR P, ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_exists_archDatumR_W_ne_zero.solution
