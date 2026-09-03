import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal
  NumberField.InfinitePlace LanglandsTunnell.Converse LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.inducedE_inducedCoeff_inv_eq_of_not_isBadPlace
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    inducedE3 ℚ (inducedCoeff K μ) v ≠ 0 ∧
    ‖inducedE3 ℚ (inducedCoeff K μ) v‖ = 1 ∧
    inducedE1 ℚ (inducedCoeff K μ⁻¹) v = inducedE2 ℚ (inducedCoeff K μ) v * (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    inducedE2 ℚ (inducedCoeff K μ⁻¹) v = inducedE1 ℚ (inducedCoeff K μ) v * (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    inducedE3 ℚ (inducedCoeff K μ⁻¹) v = (inducedE3 ℚ (inducedCoeff K μ) v)⁻¹ ∧
    ‖inducedE1 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 3 ∧ ‖inducedE2 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 3 ∧
    ‖inducedE3 ℚ (inducedCoeff K μ⁻¹) v‖ ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedE_inducedCoeff_inv_eq_of_not_isBadPlace.solution
