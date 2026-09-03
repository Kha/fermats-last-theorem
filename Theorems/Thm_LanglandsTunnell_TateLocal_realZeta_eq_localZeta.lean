import Definitions.Def_LanglandsTunnell_ArchPlace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta

set_option autoImplicit false
open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped NNReal

theorem LanglandsTunnell.TateLocal.realZeta_eq_localZeta
    (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) :
    realZeta μ f χ s = localZeta μ f χ s := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta.solution
