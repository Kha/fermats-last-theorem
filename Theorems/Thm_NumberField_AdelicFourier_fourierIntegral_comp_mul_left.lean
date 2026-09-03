import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
attribute [-instance] instCountableOfNumberField_definitions

open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.fourierIntegral_comp_mul_left (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (f : AdeleRing (𝓞 F) F → ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (w : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.solution
