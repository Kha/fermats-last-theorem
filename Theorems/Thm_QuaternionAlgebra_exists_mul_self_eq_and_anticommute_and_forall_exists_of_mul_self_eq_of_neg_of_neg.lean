import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg
    {c d : ℚ} (hc : c < 0) (hd : d < 0) (y : ℍ[ℚ, c, d]) (t : ℚ) (ht : t < 0)
    (hy : y * y = algebraMap ℚ ℍ[ℚ, c, d] t) :
    ∃ (z : ℍ[ℚ, c, d]) (c' : ℚ), c' < 0 ∧ z * z = algebraMap ℚ ℍ[ℚ, c, d] c' ∧ y * z = -(z * y) ∧
      ∀ u : ℍ[ℚ, c, d], ∃ α β γ δ : ℚ, u = α • 1 + β • y + γ • z + δ • (y * z) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_mul_self_eq_and_anticommute_and_forall_exists_of_mul_self_eq_of_neg_of_neg.solution
