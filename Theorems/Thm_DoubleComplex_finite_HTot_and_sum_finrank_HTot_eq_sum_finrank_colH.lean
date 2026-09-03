import Mathlib
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import P2M.Util
import P2M.Sol.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH

set_option autoImplicit false

universe u

theorem DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH
    {k : Type u} [Field k] (D : DoubleComplex.Bounded k)
    (hcol : ∀ p q : ℕ, Module.Finite k (DoubleComplex.colH D p q)) :
    (∀ n : ℕ, Module.Finite k (DoubleComplex.HTot D n)) ∧
      ∑ n ∈ Finset.range (2 * D.N), (-1 : ℤ) ^ n * (Module.finrank k (DoubleComplex.HTot D n) : ℤ) =
        ∑ p ∈ Finset.range D.N, ∑ q ∈ Finset.range D.N,
          (-1 : ℤ) ^ (p + q) * (Module.finrank k (DoubleComplex.colH D p q) : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_DoubleComplex_finite_HTot_and_sum_finrank_HTot_eq_sum_finrank_colH.solution
