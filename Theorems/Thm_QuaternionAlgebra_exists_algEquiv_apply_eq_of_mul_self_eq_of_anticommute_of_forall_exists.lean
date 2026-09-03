import Mathlib
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists
    {a b : ℚ} (t s : ℚ) (ht : t ≠ 0) (hs : s ≠ 0) (x w : ℍ[ℚ, a, b])
    (hx : x * x = algebraMap ℚ ℍ[ℚ, a, b] t) (hw : w * w = algebraMap ℚ ℍ[ℚ, a, b] s) (hxw : x * w = -(w * x))
    (hspan : ∀ u : ℍ[ℚ, a, b], ∃ α β γ δ : ℚ, u = α • 1 + β • x + γ • w + δ • (x * w)) :
    ∃ e : ℍ[ℚ, t, s] ≃ₐ[ℚ] ℍ[ℚ, a, b], e ⟨0, 1, 0, 0⟩ = x ∧ e ⟨0, 0, 1, 0⟩ = w := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_exists_algEquiv_apply_eq_of_mul_self_eq_of_anticommute_of_forall_exists.solution
