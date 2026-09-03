import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalWeightedOrbital_exists_isCompact_forall_halfWeighted_ne_zero_mem_and_forall_exists_nhds_halfWeighted_eq_of_isLocalTestFn
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.LocalWeightedOrbital.exists_isCompact_forall_halfWeighted_ne_zero_mem_and_forall_exists_nhds_halfWeighted_eq_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : MeasureTheory.Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f) :
    letI := AutomorphicForm.localGLBorel K v
    (∃ S : Set ((v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ), IsCompact S ∧
      ∀ a t : (v.adicCompletion K)ˣ,
        AutomorphicForm.LocalWeightedOrbital.halfWeighted
            ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
            (fun x : v.adicCompletion K => ‖x‖) f a (a * t) ≠ 0 → (a, t) ∈ S) ∧
    (∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
      ∃ V ∈ nhds (a, t), ∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p ∈ V →
        AutomorphicForm.LocalWeightedOrbital.halfWeighted
            ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
            (fun x : v.adicCompletion K => ‖x‖) f p.1 (p.1 * p.2) =
        AutomorphicForm.LocalWeightedOrbital.halfWeighted
            ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
            (fun x : v.adicCompletion K => ‖x‖) f a (a * t)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalWeightedOrbital_exists_isCompact_forall_halfWeighted_ne_zero_mem_and_forall_exists_nhds_halfWeighted_eq_of_isLocalTestFn.solution
