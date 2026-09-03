import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_inducedE_inv_eq_of_finrank_eq_three

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.inducedE_inv_eq_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3) (c : HeightOneSpectrum (𝓞 K) → ℂ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hp : ¬ IsRamifiedIn K p) (hc : ∀ 𝔓 ∈ primeFibre ℚ K p, c 𝔓 ≠ 0) :
    inducedE3 ℚ c p ≠ 0 ∧
      inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = inducedE2 ℚ c p * (inducedE3 ℚ c p)⁻¹ ∧
      inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = inducedE1 ℚ c p * (inducedE3 ℚ c p)⁻¹ ∧
      inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) p = (inducedE3 ℚ c p)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_inducedE_inv_eq_of_finrank_eq_three.solution
