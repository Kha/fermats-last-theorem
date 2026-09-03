import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    ∑ᶠ 𝔓 ∈ primeFibre ℚ K v, v.asIdeal.inertiaDeg' 𝔓.asIdeal = 3 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_finsum_primeFibre_inertiaDeg_eq_three_of_not_isRamifiedIn.solution
