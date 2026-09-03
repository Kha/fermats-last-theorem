import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.isCompact_localMaximalCompact3 (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsCompact ((localMaximalCompact3 (𝓞 ℚ) ℚ v : Subgroup (LocalGL3 v)) : Set (LocalGL3 v)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3.solution
