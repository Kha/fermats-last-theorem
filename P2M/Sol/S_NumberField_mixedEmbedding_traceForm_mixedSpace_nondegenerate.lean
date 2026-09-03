import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import P2M.Util
namespace P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding Module
open scoped Classical

theorem solution
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ (latticeBasis K)
  have h : LinearMap.BilinForm.toMatrix (latticeBasis K) (Algebra.traceForm ℝ (mixedSpace K))
      = (Algebra.traceMatrix ℚ (integralBasis K)).map (algebraMap ℚ ℝ) := by
    ext i j
    rw [Algebra.traceForm_toMatrix, Matrix.map_apply, Algebra.traceMatrix_apply,
      latticeBasis_apply, latticeBasis_apply, ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding,
      Algebra.traceForm_apply, eq_ratCast]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Algebra.discr_def, map_ne_zero]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)
