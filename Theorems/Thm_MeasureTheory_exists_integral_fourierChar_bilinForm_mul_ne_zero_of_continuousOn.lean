import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import P2M.Util
import P2M.Sol.S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (G : V → ℂ) (_hG : Integrable G μ)
    (U : Set V) (_hU : IsOpen U) (_hGU : ContinuousOn G U)
    (z₀ : V) (_hz₀ : z₀ ∈ U) (_h0 : G z₀ ≠ 0) :
    ∃ u : V, ∫ z, ((Real.fourierChar (B z u) : Circle) : ℂ) * G z ∂μ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn.solution
