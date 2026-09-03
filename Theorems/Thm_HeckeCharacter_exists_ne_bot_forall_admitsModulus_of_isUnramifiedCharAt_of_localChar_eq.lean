import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HeckeCharacter_FiniteOrder
import P2M.Util
import P2M.Sol.S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal

theorem HeckeCharacter.exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      ∀ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        Continuous (fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) →
        IsUnitaryChar (𝓞 K) K χ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → IsUnramifiedCharAt χ v) →
        (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          localChar χ v u = ρ v u) →
        HeckeCharacter.AdmitsModulus K χ 𝔣 := by p2m_exact_reverting @_root_.P2MW.S_HeckeCharacter_exists_ne_bot_forall_admitsModulus_of_isUnramifiedCharAt_of_localChar_eq.solution
