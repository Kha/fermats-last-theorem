import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg LanglandsTunnell.TateLocal

theorem LanglandsTunnell.CubicInduction.one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hram : IsRamifiedIn K v) :
    (1 : ℤ) ≤ ∑ᶠ w ∈ LanglandsTunnell.RankinSelberg.primeFibre ℚ K v,
      (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_one_le_finsum_inertiaDeg_mul_pinnedExp_of_isRamifiedIn.solution
