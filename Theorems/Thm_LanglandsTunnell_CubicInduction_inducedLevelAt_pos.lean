import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedLevelAt_pos

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.inducedLevelAt_pos (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : IsTwistRamifiedAbove K μ v) :
    0 < inducedLevelAt K μ v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedLevelAt_pos.solution
