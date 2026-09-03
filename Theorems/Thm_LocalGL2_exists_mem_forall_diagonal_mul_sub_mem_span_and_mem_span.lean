import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import P2M.Util
import P2M.Sol.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LocalGL2.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (hψ : ψ ≠ 1)
    (hψ0 : ∀ᶠ t in nhds (0 : v.adicCompletion K), ψ t = 1)
    (S : Submodule ℂ (GL (Fin 2) (v.adicCompletion K) → ℂ))
    (hstab : ∀ U ∈ S, ∀ k : GL (Fin 2) (v.adicCompletion K), (fun g => U (g * k)) ∈ S)
    (W : GL (Fin 2) (v.adicCompletion K) → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K₀ : Subgroup (GL (Fin 2) (v.adicCompletion K)),
      IsOpen (K₀ : Set (GL (Fin 2) (v.adicCompletion K))) ∧ ∀ k ∈ K₀, (fun g => W (g * k)) = W)
    (a₀ : v.adicCompletion K) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ W' ∈ S, ∀ t : GL (Fin 2) (v.adicCompletion K),
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = 1 →
      (Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (v.adicCompletion K) → ℂ | ∃ U ∈ S, ∃ x : v.adicCompletion K,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}) ∧
      (¬ Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (v.adicCompletion K) → ℂ | ∃ U ∈ S, ∃ x : v.adicCompletion K,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - ψ x • U}) := by p2m_exact_reverting @_root_.P2MW.S_LocalGL2_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span.solution
