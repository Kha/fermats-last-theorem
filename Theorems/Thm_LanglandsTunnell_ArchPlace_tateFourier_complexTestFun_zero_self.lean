import Definitions.Def_LanglandsTunnell_ArchPlace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self

set_option autoImplicit false

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

theorem LanglandsTunnell.ArchPlace.tateFourier_complexTestFun_zero_self :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun 0) = complexTestFun 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_complexTestFun_zero_self.solution
