import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_ArchPlace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchPlace_tateFourier_psiComplex_complexTestFun
attribute [-simp] LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq

set_option autoImplicit false

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

theorem LanglandsTunnell.ArchPlace.tateFourier_psiComplex_complexTestFun (k : ℤ) (w : ℂ) :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun k) w
      = (-Complex.I) ^ k.natAbs * complexTestFun (-k) w := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiComplex_complexTestFun.solution
