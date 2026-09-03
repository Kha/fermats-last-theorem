import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_IdeleBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
open scoped NNReal

theorem AutomorphicForm.exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
    (K : Type) [Field K] [NumberField K]
    (ω₁ ω₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (hω₁ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω₁ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hω₂ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω₂ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hω₁c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ω₁ z : ℂˣ) : ℂ))
    (hω₂c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ω₂ z : ℂˣ) : ℂ))
    (hω₁F : IsIdeleClassChar (𝓞 K) K ω₁) (hω₂F : IsIdeleClassChar (𝓞 K) K ω₂)
    (N₁ N₂ : Ideal (𝓞 K)) (hN₁ : N₁ ≠ ⊥) (hN₂ : N₂ ≠ ⊥)
    (hmod₁ : HeckeCharacter.AdmitsModulus K ω₁ N₁) (hmod₂ : HeckeCharacter.AdmitsModulus K ω₂ N₂) :
    ∃ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsUnitaryChar (𝓞 K) K ν ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ω₁ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (n : ℕ), HeckeCharacter.idealMultiplicity K v N₁ ≤ n →
        HeckeCharacter.idealMultiplicity K v N₂ ≤ n → 1 ≤ n →
        ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          NumberField.TateGlobal.localChar ν v t = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ N₁ → ¬ v.asIdeal ∣ N₂ →
        NumberField.TateGlobal.IsUnramifiedCharAt ν v) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus.solution
