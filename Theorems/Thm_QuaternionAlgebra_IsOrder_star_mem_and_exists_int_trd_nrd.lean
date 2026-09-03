import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.star_mem_and_exists_int_trd_nrd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    star x ∈ Λ ∧ ∃ t n : ℤ, trd x = (t : ℚ) ∧ nrd x = (n : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_IsOrder_star_mem_and_exists_int_trd_nrd.solution
