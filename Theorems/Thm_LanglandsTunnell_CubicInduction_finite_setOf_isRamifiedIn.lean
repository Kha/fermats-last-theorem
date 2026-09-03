import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.finite_setOf_isRamifiedIn
    (K : Type) [Field K] [NumberField K] :
    {v : HeightOneSpectrum (𝓞 ℚ) | IsRamifiedIn K v}.Finite := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_finite_setOf_isRamifiedIn.solution
