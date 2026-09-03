import Definitions.Def_LanglandsTunnell_JLConverse
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.ArchDatumC.zetaEntire_diagOne_mul {P : ComplexArchParam} (D : ArchDatumC P)
    (g : Matrix (Fin 2) (Fin 2) ℂ) (A : ℂ) (u : ℂ) (k : ℤ) (s : ℂ) (hA : A ≠ 0) (hg : g.det ≠ 0) :
    D.zetaEntire (ArchC.diagOne A * g) u k s =
      (ArchC.quasiChar u k A)⁻¹ * ((‖A‖ ^ 2 : ℝ) : ℂ) ^ (1 - s) * D.zetaEntire g u k s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_ArchDatumC_zetaEntire_diagOne_mul.solution
