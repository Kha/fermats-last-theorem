import Mathlib
import P2M.Util
import P2M.Sol.S_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four

set_option autoImplicit false

open scoped Quaternion

theorem exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
    (D : Type*) [Ring D] [Algebra ℚ D] (hdim : Module.finrank ℚ D = 4)
    (hdiv : ∀ x : D, x ≠ 0 → IsUnit x)
    (hcen : ∀ z : D, (∀ x : D, z * x = x * z) → z ∈ Set.range (algebraMap ℚ D)) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) := by p2m_exact_reverting @_root_.P2MW.S_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four.solution
