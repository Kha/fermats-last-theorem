import Mathlib
import P2M.Util
import P2M.Sol.S_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real

theorem QuadraticForm.exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (c : ℚ) (hc : c ≠ 0)
    (hv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      ∃ x y z : v.adicCompletion ℚ,
        -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
          + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2
          = algebraMap ℚ (v.adicCompletion ℚ) c)
    (hR : ∃ x y z : ℝ, -(algebraMap ℚ ℝ a) * x ^ 2 - (algebraMap ℚ ℝ b) * y ^ 2
        + (algebraMap ℚ ℝ a) * (algebraMap ℚ ℝ b) * z ^ 2 = algebraMap ℚ ℝ c) :
    ∃ x y z : ℚ, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c := by p2m_exact_reverting @_root_.P2MW.S_QuadraticForm_exists_rat_ternary_pureNrd_eq_of_forall_adicCompletion_of_real.solution
