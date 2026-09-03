import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq

open scoped Quaternion
theorem QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ t n : ℤ, QuaternionAlgebra.trd x = t ∧ QuaternionAlgebra.nrd x = n) ∧
      (∀ r : ℚ, r • (1 : ℍ[ℚ, a, b]) ∈ Λ → ∃ k : ℤ, (k : ℚ) = r) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq.solution
