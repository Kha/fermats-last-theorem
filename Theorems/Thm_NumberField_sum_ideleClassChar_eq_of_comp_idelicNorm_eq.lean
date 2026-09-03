import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false

open NumberField

theorem NumberField.sum_ideleClassChar_eq_of_comp_idelicNorm_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩)) :
    (∀ (a : Kˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ∑ ξ ∈ Ξ, ((ξ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
        (Ξ.card : ℂ) * ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
    (∀ u : (AdeleRing (𝓞 K) K)ˣ,
      u ∉ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range →
        ∑ ξ ∈ Ξ, ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ) = 0) ∧
    (Ξ.Nonempty → Ξ.card =
      ((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔
        (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range).index) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq.solution
