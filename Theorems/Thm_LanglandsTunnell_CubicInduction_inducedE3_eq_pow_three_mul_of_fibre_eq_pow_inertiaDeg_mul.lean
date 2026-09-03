import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul
    (K : Type) [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (c c' : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ w ∈ primeFibre ℚ K v,
      c' w = (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) * c w) :
    inducedE3 ℚ c' v = (χ (uniformizerIdele ℚ v) : ℂ) ^ 3 * inducedE3 ℚ c v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_eq_pow_three_mul_of_fibre_eq_pow_inertiaDeg_mul.solution
