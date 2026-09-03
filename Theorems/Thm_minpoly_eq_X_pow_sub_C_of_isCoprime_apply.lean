import Mathlib
import P2M.Util
import P2M.Sol.S_minpoly_eq_X_pow_sub_C_of_isCoprime_apply

open Polynomial

theorem minpoly.eq_X_pow_sub_C_of_isCoprime_apply
    {F L : Type*} [Field F] [Ring L] [Nontrivial L] [Algebra F L]
    (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {u : F} (hu : u ≠ 0) (hcop : IsCoprime (v u) n)
    (θ : L) (hθ : θ ^ n = algebraMap F L u) :
    minpoly F θ = X ^ n - C u := by p2m_exact_reverting @_root_.P2MW.S_minpoly_eq_X_pow_sub_C_of_isCoprime_apply.solution
