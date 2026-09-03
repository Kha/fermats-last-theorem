import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_ArchPlace
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor
attribute [-simp] LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq

set_option autoImplicit false

open MeasureTheory NumberField LanglandsTunnell.ArchPlace

open scoped Classical in

theorem LanglandsTunnell.ArchPlace.fourierIntegral_mixedSpace_pureTensor
    (K : Type) [Field K] [NumberField K]
    (a : {w : InfinitePlace K // w.IsReal} → ZMod 2) (k : {w : InfinitePlace K // w.IsComplex} → ℤ)
    (ψ : AddChar (mixedEmbedding.mixedSpace K) ℂ)
    (hψ : ∀ v : mixedEmbedding.mixedSpace K,
      ψ v = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace K) v) : ℂ))
    (x : mixedEmbedding.mixedSpace K) :
    NumberField.AdelicFourier.fourierIntegral ψ volume
        (fun v => (∏ w, realTestFun (a w) (v.1 w)) * ∏ w, complexTestFun (k w) (v.2 w)) x
      = (∏ w, (-Complex.I) ^ (a w).val) * (∏ w, (-Complex.I) ^ (k w).natAbs)
          * (1 / 2 : ℂ) ^ InfinitePlace.nrComplexPlaces K
          * ((∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (-k w) (x.2 w)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor.solution
