import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hu : WhittakerBlock.IsArchSmooth3 u) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.IsArchSmooth3 (fun g => u (g * k)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right.solution
