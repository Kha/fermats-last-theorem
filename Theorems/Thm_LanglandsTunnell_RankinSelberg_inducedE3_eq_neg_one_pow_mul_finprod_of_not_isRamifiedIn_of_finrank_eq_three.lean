import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsRamifiedIn K v) :
    inducedE3 ℚ c v = (-1) ^ (Nat.card (primeFibre ℚ K v) + 1) * ∏ᶠ w ∈ primeFibre ℚ K v, c w := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_inducedE3_eq_neg_one_pow_mul_finprod_of_not_isRamifiedIn_of_finrank_eq_three.solution
