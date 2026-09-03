import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumC_exists_W_eq_fderivWithin_mul

set_option autoImplicit false
open LanglandsTunnell LanglandsTunnell.Converse in

theorem LanglandsTunnell.Converse.ArchDatumC.exists_W_eq_fderivWithin_mul
    (P : ComplexArchParam) (d : ArchDatumC P) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ d' : ArchDatumC P, ∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.det ≠ 0 →
      d'.W g = fderivWithin ℝ (ArchC.asPi d.W) ArchC.glSet (Matrix.of.symm g) (Matrix.of.symm (g * X)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumC_exists_W_eq_fderivWithin_mul.solution
