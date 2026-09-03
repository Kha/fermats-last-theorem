import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumR_zetaEntire_diagOne_mul

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumR.zetaEntire_diagOne_mul {P : RealArchParam} (D : ArchDatumR P)
    (g : Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ) (u : ℂ) (a : ZMod 2) (s : ℂ) (hA : A ≠ 0) (hg : g.det ≠ 0) :
    D.zetaEntire (ArchR.diagOne A * g) u a s =
      (ArchR.quasiChar u a A)⁻¹ * ((|A| : ℝ) : ℂ) ^ (1 - s) * D.zetaEntire g u a s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumR_zetaEntire_diagOne_mul.solution
