import Mathlib
import P2M.Util
import P2M.Sol.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split

theorem QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ¬ Nonempty (QuaternionAlgebra (v.adicCompletion ℚ)
        (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b)
          ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (c : v.adicCompletion ℚ) (hc : ¬ IsSquare (-c)) :
    ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2 = c := by p2m_exact_reverting @_root_.P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.solution
