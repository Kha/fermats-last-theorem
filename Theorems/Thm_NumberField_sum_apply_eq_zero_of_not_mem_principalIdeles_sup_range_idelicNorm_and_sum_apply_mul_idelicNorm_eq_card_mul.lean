import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
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
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) →
        ∑ ξ ∈ Ξ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = 0) ∧
    (∀ (k : Kˣ) (w : (AdeleRing (𝓞 L) L)ˣ),
      ∑ ξ ∈ Ξ, ((ξ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
        (Ξ.card : ℂ) * ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul.solution
