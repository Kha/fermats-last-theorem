import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v}.Finite := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous.solution
