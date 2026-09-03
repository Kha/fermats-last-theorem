import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate

open NumberField NumberField.mixedEmbedding
open scoped Classical
theorem NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate.solution
