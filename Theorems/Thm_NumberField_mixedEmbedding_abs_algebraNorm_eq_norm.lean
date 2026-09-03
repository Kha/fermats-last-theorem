import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_abs_algebraNorm_eq_norm

set_option autoImplicit false

open NumberField

theorem NumberField.mixedEmbedding.abs_algebraNorm_eq_norm
    (K : Type) [Field K] [NumberField K] (x : mixedEmbedding.mixedSpace K) :
    |Algebra.norm ℝ x| = mixedEmbedding.norm x := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_abs_algebraNorm_eq_norm.solution
