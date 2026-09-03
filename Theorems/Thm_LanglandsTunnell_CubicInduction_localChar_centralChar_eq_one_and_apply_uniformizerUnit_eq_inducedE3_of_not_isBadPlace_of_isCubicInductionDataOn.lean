import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal NumberField.AdelicLevel AutomorphicForm
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (pins : CarrierPins ℚ) (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (hF : X.form ≠ 0)
    (T₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT₀ : ∀ v, IsBadPlace K μ v → v ∈ T₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ IsBadPlace K μ v) :
    (∀ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 →
        localChar X.centralChar v u = 1) ∧
      ((localChar X.centralChar v (uniformizerUnit ℚ v) : ℂˣ) : ℂ) =
        inducedE3 ℚ (inducedCoeff K μ) v := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localChar_centralChar_eq_one_and_apply_uniformizerUnit_eq_inducedE3_of_not_isBadPlace_of_isCubicInductionDataOn.solution
