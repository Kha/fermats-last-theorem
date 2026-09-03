import Definitions.Def_LanglandsTunnell_CubicInduction_LocalWhittakerDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction
  LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker

theorem LanglandsTunnell.CubicInduction.inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hram : IsRamifiedIn K v) :
    LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedE3_eq_zero_of_isRamifiedIn_of_finrank_eq_three.solution
