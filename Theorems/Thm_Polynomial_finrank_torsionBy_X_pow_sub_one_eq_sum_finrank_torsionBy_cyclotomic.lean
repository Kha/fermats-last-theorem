import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum
theorem Polynomial.finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {e : ℕ} (he : 0 < e) :
    Module.finrank ℚ (Submodule.torsionBy ℚ[X] M ((X : ℚ[X]) ^ e - 1)) =
      ∑ d ∈ e.divisors, Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_finrank_torsionBy_X_pow_sub_one_eq_sum_finrank_torsionBy_cyclotomic.solution
