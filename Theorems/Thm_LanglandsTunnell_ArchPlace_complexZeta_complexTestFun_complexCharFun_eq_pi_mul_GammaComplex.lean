import Definitions.Def_LanglandsTunnell_ArchPlace
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchPlace_complexZeta_complexTestFun_complexCharFun_eq_pi_mul_GammaComplex
attribute [-simp] LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq

set_option autoImplicit false

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

theorem
LanglandsTunnell.ArchPlace.complexZeta_complexTestFun_complexCharFun_eq_pi_mul_GammaComplex
    (u : ℂ) (k : ℤ) (s : ℂ)
    (hs : 0 < (s + (u + (k.natAbs : ℂ) / 2)).re) :
    complexZeta ((2 : ℝ≥0∞) • volume) (complexTestFun k) (complexCharFun u k) s
      = (Real.pi : ℂ) * Complex.Gammaℂ (s + (u + (k.natAbs : ℂ) / 2)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_complexZeta_complexTestFun_complexCharFun_eq_pi_mul_GammaComplex.solution
