import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal

set_option autoImplicit false

open MeasureTheory NumberField

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal
    (K : Type) [Field K] [NumberField K] (i₀ : {v : NumberField.InfinitePlace K // v.IsReal}) :
    ∃ e : NumberField.mixedEmbedding.mixedSpace K ≃L[ℝ] (ℝ × (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ i₀} → ℝ) × ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ))),
      MeasurePreserving e volume volume ∧
      ∀ X : NumberField.mixedEmbedding.mixedSpace K, (e X).1 = X.1 i₀ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal.solution
