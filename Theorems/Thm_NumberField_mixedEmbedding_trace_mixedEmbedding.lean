import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_trace_mixedEmbedding

open NumberField NumberField.mixedEmbedding
open scoped Classical
theorem NumberField.mixedEmbedding.trace_mixedEmbedding
    (K : Type*) [Field K] [NumberField K] (x : K) :
    Algebra.trace ℝ (mixedSpace K) (mixedEmbedding K x) = (Algebra.trace ℚ K x : ℝ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_trace_mixedEmbedding.solution
