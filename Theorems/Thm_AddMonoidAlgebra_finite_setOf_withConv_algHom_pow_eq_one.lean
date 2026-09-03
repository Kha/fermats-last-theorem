import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidAlgebra_finite_setOf_withConv_algHom_pow_eq_one

set_option autoImplicit false

universe u

theorem AddMonoidAlgebra.finite_setOf_withConv_algHom_pow_eq_one
    (κ : Type u) [CommRing κ] [IsDomain κ] (t n : ℕ) (hn : 0 < n) :
    {χ : WithConv (AddMonoidAlgebra κ (Fin t → ℤ) →ₐ[κ] κ) | χ ^ n = 1}.Finite := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidAlgebra_finite_setOf_withConv_algHom_pow_eq_one.solution
