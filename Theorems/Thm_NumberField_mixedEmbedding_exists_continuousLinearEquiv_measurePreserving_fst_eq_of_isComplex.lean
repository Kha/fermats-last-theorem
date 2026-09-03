import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex

set_option autoImplicit false

open MeasureTheory NumberField

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex
    (K : Type) [Field K] [NumberField K] (i₀ : {v : NumberField.InfinitePlace K // v.IsComplex}) :
    ∃ e : NumberField.mixedEmbedding.mixedSpace K ≃L[ℝ] (ℂ × (({v : NumberField.InfinitePlace K // v.IsReal} → ℝ) × ({w : {w : NumberField.InfinitePlace K // w.IsComplex} // w ≠ i₀} → ℂ))),
      MeasurePreserving e volume volume ∧
      ∀ X : NumberField.mixedEmbedding.mixedSpace K, (e X).1 = X.2 i₀ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex.solution
