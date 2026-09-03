import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq

set_option autoImplicit false
universe u v
open Polynomial Module
open scoped DirectSum
theorem Polynomial.nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq
    {M : Type u} [AddCommGroup M] [Module ℚ[X] M] [Module ℚ M] [IsScalarTower ℚ ℚ[X] M] [FiniteDimensional ℚ M]
    {N : Type v} [AddCommGroup N] [Module ℚ[X] N] [Module ℚ N] [IsScalarTower ℚ ℚ[X] N] [FiniteDimensional ℚ N]
    {n : ℕ} (hn : 0 < n) (hM : Module.IsTorsionBy ℚ[X] M ((X : ℚ[X]) ^ n - 1)) (hN : Module.IsTorsionBy ℚ[X] N ((X : ℚ[X]) ^ n - 1))
    (h : ∀ d, d ∣ n → Module.finrank ℚ (Submodule.torsionBy ℚ[X] M (cyclotomic d ℚ)) =
      Module.finrank ℚ (Submodule.torsionBy ℚ[X] N (cyclotomic d ℚ))) :
    Nonempty (M ≃ₗ[ℚ[X]] N) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_nonempty_linearEquiv_of_finrank_torsionBy_cyclotomic_eq.solution
