import Definitions.Def_LanglandsTunnell_ArchPlace
import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal
attribute [-simp] LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero

set_option autoImplicit false

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

theorem LanglandsTunnell.ArchPlace.realZeta_realTestFun_realCharFun_eq_GammaReal (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hs : 0 < (s + (u + signShift a)).re) :
    realZeta volume (realTestFun a) (realCharFun u a) s = Complex.Gammaℝ (s + (u + signShift a)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.solution
