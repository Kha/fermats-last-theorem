import Mathlib
import Theorems.Thm_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply
import P2M.Util
namespace P2MW.S_minpoly_eq_X_pow_sub_C_of_isCoprime_apply

set_option autoImplicit false

open Polynomial

theorem solution
    {F L : Type*} [Field F] [Ring L] [Nontrivial L] [Algebra F L]
    (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {u : F} (hu : u ≠ 0) (hcop : IsCoprime (v u) n)
    (θ : L) (hθ : θ ^ n = algebraMap F L u) :
    minpoly F θ = X ^ n - C u := by
  refine (minpoly.eq_of_irreducible_of_monic
    (Polynomial.X_pow_sub_C_irreducible_of_isCoprime_apply v hv hn hu hcop) ?_
    (monic_X_pow_sub_C u hn.ne')).symm
  rw [map_sub, map_pow, aeval_X, aeval_C, hθ, sub_self]
