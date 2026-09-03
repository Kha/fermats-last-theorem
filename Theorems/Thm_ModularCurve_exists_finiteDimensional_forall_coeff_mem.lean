import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_finiteDimensional_forall_coeff_mem

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_finiteDimensional_forall_coeff_mem (N : ℕ)
    (f : modularFunctionFieldBar N) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      ∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_finiteDimensional_forall_coeff_mem.solution
