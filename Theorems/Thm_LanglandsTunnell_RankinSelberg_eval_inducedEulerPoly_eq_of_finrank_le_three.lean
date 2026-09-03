import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K ≤ 3)
    {R : Type*} [CommRing R] (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 ℚ)) (z : R) :
    (inducedEulerPoly ℚ c p).eval z =
      1 - inducedE1 ℚ c p * z + inducedE2 ℚ c p * z ^ 2 - inducedE3 ℚ c p * z ^ 3 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three.solution
