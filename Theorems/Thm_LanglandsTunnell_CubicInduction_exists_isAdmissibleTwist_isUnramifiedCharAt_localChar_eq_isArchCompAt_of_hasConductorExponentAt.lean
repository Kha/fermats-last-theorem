import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

theorem LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∃ c : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ c)
    (e : ℤ) (he : ((χ (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ e) :
    ∃ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ τ ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ≠ v → IsUnramifiedCharAt τ p) ∧
      (∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
        ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
        TateGlobal.localChar τ v u = χ u) ∧
      (∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 e) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_exists_isAdmissibleTwist_isUnramifiedCharAt_localChar_eq_isArchCompAt_of_hasConductorExponentAt.solution
