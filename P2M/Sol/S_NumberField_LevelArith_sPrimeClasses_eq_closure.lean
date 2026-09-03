import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
namespace P2MW.S_NumberField_LevelArith_sPrimeClasses_eq_closure

set_option autoImplicit false
open NumberField.LevelArith
open scoped NumberField.LevelArith

namespace L3XSPrime

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

variable (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F]

noncomputable def mapPlace (σ : F ≃ₐ[E] F) (w : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.map (ringOfIntegersAut E F σ : 𝓞 F →+* 𝓞 F)
  isPrime := Ideal.map_isPrime_of_equiv (ringOfIntegersAut E F σ)
  ne_bot := fun h => w.ne_bot ((Ideal.map_eq_bot_iff_of_injective (ringOfIntegersAut E F σ).injective).1 h)

theorem smul_primeClass (σ : F ≃ₐ[E] F) (w : HeightOneSpectrum (𝓞 F)) : σ • primeClass F w = primeClass F (mapPlace E F σ w) := by
  rw [primeClass, smul_mk0]
  rfl

theorem mapPlace_mem {S : Set Nat.Primes} (σ : F ≃ₐ[E] F) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ placesOverPrimes F S) :
    mapPlace E F σ w ∈ placesOverPrimes F S := by
  obtain ⟨p, hp, hpw⟩ := hw
  refine ⟨p, hp, ?_⟩
  have h := Ideal.mem_map_of_mem (ringOfIntegersAut E F σ : 𝓞 F →+* 𝓞 F) hpw
  rwa [map_natCast] at h

theorem image_subset (S : Set Nat.Primes) (σ : F ≃ₐ[E] F) :
    (MulDistribMulAction.toMonoidHom (ClassGroup (𝓞 F)) σ) '' (primeClass F '' placesOverPrimes F S) ⊆ primeClass F '' placesOverPrimes F S := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨mapPlace E F σ w, mapPlace_mem E F σ hw, (smul_primeClass E F σ w).symm⟩

end L3XSPrime

theorem solution
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (S : Set Nat.Primes) :
    sPrimeClasses E F S = Subgroup.closure (primeClass F '' placesOverPrimes F S) := by
  apply le_antisymm
  · intro c hc
    have h := (mem_sPrimeClasses_iff E F S c).1 hc 1
    rwa [one_smul] at h
  · refine le_iInf fun σ => ?_
    rw [← Subgroup.map_le_iff_le_comap, MonoidHom.map_closure]
    exact Subgroup.closure_mono (L3XSPrime.image_subset E F S σ)
