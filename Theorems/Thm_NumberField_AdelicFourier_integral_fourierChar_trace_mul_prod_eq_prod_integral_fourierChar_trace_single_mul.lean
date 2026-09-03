import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.Analysis.Complex.Circle
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.AdelicFourier.integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)]
    (μ : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, SigmaFinite (μ w)]
    (g : (w : InfinitePlace F) → w.Completion → ℂ) (ξ : InfiniteAdeleRing F) :
    ∫ y : InfiniteAdeleRing F,
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
            (InfiniteAdeleRing.ringEquiv_mixedSpace F (-(y * ξ)))) : ℂ) * ∏ w, g w (y w) ∂(Measure.pi μ)
      = ∏ w, ∫ z, (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
            (InfiniteAdeleRing.ringEquiv_mixedSpace F (Pi.single w (-(z * ξ w))))) : ℂ) * g w z ∂(μ w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_integral_fourierChar_trace_mul_prod_eq_prod_integral_fourierChar_trace_single_mul.solution
