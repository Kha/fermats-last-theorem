import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import P2M.Util
import P2M.Sol.S_NumberField_exists_valuationSubring_eq_localization
attribute [-instance] AlgebraicClosure.Rat.isGalois

open scoped NumberField Pointwise
theorem NumberField.exists_valuationSubring_eq_localization
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_valuationSubring_eq_localization.solution
