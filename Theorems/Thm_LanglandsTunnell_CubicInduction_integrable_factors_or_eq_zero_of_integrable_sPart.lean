import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.integrable_factors_or_eq_zero_of_integrable_sPart
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (finf : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (f : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ → ℂ)
    (hinf : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, finf a = finf (NumberField.Idele.partAt ℚ ∅ a))
    (hprod : Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => finf a * ∏ v ∈ S, f v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v))
      (NumberField.Idele.sPartMeasure ℚ S)) :
    (Integrable finf (NumberField.Idele.sPartMeasure ℚ ∅) ∧
        ∀ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v
          Integrable (f v) (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) ∨
      finf =ᵐ[NumberField.Idele.sPartMeasure ℚ ∅] 0 ∨
      ∃ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v;
        f v =ᵐ[LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)] 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart.solution
