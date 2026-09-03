import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_localChar_centralChar_neg_one_and_pin_eq_finprod_of_eq_finprod_mul_of_isCubicInductionDataOn

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.localChar_centralChar_neg_one_and_pin_eq_finprod_of_eq_finprod_mul_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (pins : CarrierPins ℚ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X) (v : HeightOneSpectrum (𝓞 ℚ))
    (η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hη : HasConductorExponentAt ℚ v η 0) (hη2 : ∀ x, η x * η x = 1)
    (hω : ∀ x : (v.adicCompletion ℚ)ˣ,
      ((localChar X.centralChar v x : ℂˣ) : ℂ) =
        (∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
          (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom x) : ℂˣ) : ℂ)) *
          ((η x : ℂˣ) : ℂ)) :
    ((localChar X.centralChar v (-1) : ℂˣ) : ℂ) = ∏ᶠ w ∈ primeFibre ℚ K v, ((localChar μ w (-1) : ℂˣ) : ℂ) ∧
      ∀ (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ), 1 ≤ a → Even a → HasConductorExponentAt ℚ v χ a →
        ∀ c : (v.adicCompletion ℚ)ˣ,
          (∀ u ∈ higherUnitsAt ℚ v ((a - 1) / 2 + 1), (χ u : ℂ) =
            NumberField.StandardAddChar.psiLocal ℚ v ((c : v.adicCompletion ℚ) * ((u : v.adicCompletion ℚ) - 1))) →
          ((localChar X.centralChar v c : ℂˣ) : ℂ) =
            ∏ᶠ w : v.Extension (𝓞 K), ((localChar μ w.1
              (Units.map (algebraMap (v.adicCompletion ℚ) (w.1.adicCompletion K)).toMonoidHom c) : ℂˣ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_localChar_centralChar_neg_one_and_pin_eq_finprod_of_eq_finprod_mul_of_isCubicInductionDataOn.solution
