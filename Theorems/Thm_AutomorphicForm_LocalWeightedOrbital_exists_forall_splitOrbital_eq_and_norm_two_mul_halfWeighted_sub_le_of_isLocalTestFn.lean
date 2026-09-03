import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalWeightedOrbital_exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalWeightedOrbital.exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    letI := AutomorphicForm.localGLBorel K v
    ∃ C : ℝ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
      AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a (a * t) =
        AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a a ∧
      ‖2 * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f a (a * t) -
          (2 * ((Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) *
              AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a a -
            2 * ∫ x : v.adicCompletion K, AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a a x * ((Real.log ‖x‖ : ℝ) : ℂ) ∂μ)‖ ≤
        C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ * (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalWeightedOrbital_exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn.solution
