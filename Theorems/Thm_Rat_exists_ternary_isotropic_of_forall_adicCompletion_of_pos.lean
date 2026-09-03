import Mathlib
import P2M.Util
import P2M.Sol.S_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos

open IsDedekindDomain NumberField
theorem Rat.exists_ternary_isotropic_of_forall_adicCompletion_of_pos
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2
          - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2 = 0)
    (hR : 0 < a ∨ 0 < b) :
    ∃ z x y : ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rat_exists_ternary_isotropic_of_forall_adicCompletion_of_pos.solution
