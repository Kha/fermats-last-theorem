import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (hS : S.Finite) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ S X) (hform : X.form ≠ 0) :
    X.whittakerArch ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), X.whittakerLoc v ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_whittakerArch_ne_zero_and_whittakerLoc_ne_zero_of_isCubicInductionDataOn_of_form_ne_zero.solution
