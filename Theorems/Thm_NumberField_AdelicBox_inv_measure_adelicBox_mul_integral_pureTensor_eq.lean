import Definitions.Def_NumberField_AdelicBox
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import P2M.Util
import P2M.Sol.S_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq
attribute [-instance] instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox IsDedekindDomain
open scoped Classical in

theorem NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ) (g : FiniteAdeleRing (𝓞 F) F → ℂ) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹ *
        ∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * g x.2 ∂μ
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ) *
        ((∫ y, f y) * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)⁻¹ * ∫ z, g z ∂ν)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq.solution
