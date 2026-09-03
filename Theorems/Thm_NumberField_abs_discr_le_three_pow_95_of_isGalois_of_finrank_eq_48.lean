import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_abs_discr_le_three_pow_95_of_isGalois_of_finrank_eq_48

theorem NumberField.abs_discr_le_three_pow_95_of_isGalois_of_finrank_eq_48
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (h48 : Module.finrank ℚ K = 48)
    (hunr : ∀ (P : Ideal (NumberField.RingOfIntegers K)) [P.IsMaximal],
      (3 : NumberField.RingOfIntegers K) ∉ P → Algebra.IsUnramifiedAt ℤ P) :
    |NumberField.discr K| ≤ (3 : ℤ) ^ 95 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_abs_discr_le_three_pow_95_of_isGalois_of_finrank_eq_48.solution
