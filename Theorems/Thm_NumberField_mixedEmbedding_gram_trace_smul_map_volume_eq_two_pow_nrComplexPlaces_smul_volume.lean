import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume

set_option autoImplicit false

open MeasureTheory NumberField

open scoped Classical in

theorem NumberField.mixedEmbedding.gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume
    (K : Type) [Field K] [NumberField K]
    (m : ℕ) (b : Fin m → mixedEmbedding.mixedSpace K) (hb : LinearIndependent ℝ b)
    (hbsp : Submodule.span ℝ (Set.range b) = ⊤) :
    (ENNReal.ofReal (Real.sqrt |(Matrix.of fun a a' : Fin m =>
          Algebra.trace ℝ (mixedEmbedding.mixedSpace K) (b a * b a')).det|)) •
        Measure.map (fun c : Fin m → ℝ => ∑ a, c a • b a) volume =
      (2 : ENNReal) ^ NumberField.InfinitePlace.nrComplexPlaces K •
        (volume : Measure (mixedEmbedding.mixedSpace K)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_gram_trace_smul_map_volume_eq_two_pow_nrComplexPlaces_smul_volume.solution
