import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_ne_zero

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.CubicInductionForm.whittakerLoc_ne_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (F : CubicInductionForm K pins ψ μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w, IsBadPlace K μ w → w ∈ S)
    (hF : F.form ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    F.whittakerLoc v ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_CubicInductionForm_whittakerLoc_ne_zero.solution
