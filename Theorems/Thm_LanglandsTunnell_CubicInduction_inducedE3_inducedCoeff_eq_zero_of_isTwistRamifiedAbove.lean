import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedE3_inducedCoeff_eq_zero_of_isTwistRamifiedAbove

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

open AutomorphicForm LanglandsTunnell.Converse in

theorem LanglandsTunnell.CubicInduction.inducedE3_inducedCoeff_eq_zero_of_isTwistRamifiedAbove
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hram : IsTwistRamifiedAbove K μ v) (hK : ¬ IsRamifiedIn K v) :
    RankinSelberg.inducedE3 ℚ (inducedCoeff K μ) v = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_inducedCoeff_eq_zero_of_isTwistRamifiedAbove.solution
