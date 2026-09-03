import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import P2M.Util
import P2M.Sol.S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform

theorem VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (f : V → ℂ) (_hf : Integrable f μ)
    (_h : ∀ w : V, VectorFourier.fourierIntegral 𝐞 μ B f w = 0) :
    f =ᵐ[μ] 0 := by p2m_exact_reverting @_root_.P2MW.S_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero.solution
