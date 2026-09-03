import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_exists_W_eq_fderivWithin_mul

set_option autoImplicit false
open LanglandsTunnell LanglandsTunnell.Converse in

theorem LanglandsTunnell.Converse.ArchDatumR.exists_W_eq_fderivWithin_mul
    (P : RealArchParam) (d : ArchDatumR P) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ d' : ArchDatumR P, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      d'.W g = fderivWithin ℝ (ArchR.asPi d.W) ArchR.glSet (Matrix.of.symm g) (Matrix.of.symm (g * X)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_exists_W_eq_fderivWithin_mul.solution
