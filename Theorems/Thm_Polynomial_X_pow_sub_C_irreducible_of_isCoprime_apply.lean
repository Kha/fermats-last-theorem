import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply

open Polynomial

theorem Polynomial.X_pow_sub_C_irreducible_of_isCoprime_apply
    {F : Type*} [Field F] (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {a : F} (ha : a ≠ 0) (hcop : IsCoprime (v a) n) :
    Irreducible (X ^ n - C a) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply.solution
