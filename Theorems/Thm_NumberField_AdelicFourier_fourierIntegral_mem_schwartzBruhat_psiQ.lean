import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import P2M.Util
import P2M.Sol.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ

open NumberField NumberField.AdelicFourier
theorem NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_psiQ [MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)] [BorelSpace (AdeleRing (𝓞 ℚ) ℚ)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 ℚ) ℚ)) [μ.IsAddHaarMeasure] {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ schwartzBruhat ℚ) :
    fourierIntegral NumberField.StandardAddChar.psiQ μ f ∈ schwartzBruhat ℚ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_psiQ.solution
