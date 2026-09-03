import Definitions.Def_LanglandsTunnell_ConverseData
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt
attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal LanglandsTunnell.Converse

theorem HeckeCharacter.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ : (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletion ℚ)ˣ →* ℂˣ) (n : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hξ : ∀ v ∈ S, HasConductorExponentAt ℚ v (ξ v) (n v)) :
    ∃ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      IsAdmissibleTwist ℚ τ ∧
      (∀ v ∈ S, ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
        ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
          localChar τ v u = ξ v u) ∧
      (∀ v ∈ S, HasConductorExponentAt ℚ v (localChar τ v) (n v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → IsUnramifiedCharAt τ v) ∧
      ∃ e : ℤ, ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 e := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt.solution
