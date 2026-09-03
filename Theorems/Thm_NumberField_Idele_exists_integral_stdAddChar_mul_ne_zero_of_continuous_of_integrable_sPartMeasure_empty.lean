import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicTraceFin
import P2M.Util
import P2M.Sol.S_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem NumberField.Idele.exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty
    (K : Type) [Field K] [NumberField K]
    (h : (AdeleRing (𝓞 K) K)ˣ → ℂ) (_hc : Continuous h)
    (_hint : Integrable h (NumberField.Idele.sPartMeasure K ∅))
    (_hne : ∃ t₀ : (AdeleRing (𝓞 K) K)ˣ, ((t₀ : AdeleRing (𝓞 K) K)).2 = 1 ∧ h t₀ ≠ 0) :
    ∃ u : InfiniteAdeleRing K,
      ∫ t, NumberField.StandardAddChar.stdAddChar K ((((t : AdeleRing (𝓞 K) K)).1 * u, 0)) * h t
          ∂(NumberField.Idele.sPartMeasure K ∅) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_Idele_exists_integral_stdAddChar_mul_ne_zero_of_continuous_of_integrable_sPartMeasure_empty.solution
