import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace

open AlgebraicCurve
theorem AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
    {K F : Type*} [Field K] [Infinite K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (D : AlgebraicCurve.Divisor K F) (V : Submodule K F) [FiniteDimensional K ↥V]
    (hVD : V ≤ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place K F, ∃ f ∈ V, f ≠ 0 ∧ w.ord f + D w = 0) :
    ∃ f₁ ∈ V, ∃ f₂ ∈ V, ∀ w : AlgebraicCurve.Place K F,
      (f₁ ≠ 0 ∧ w.ord f₁ + D w = 0) ∨ (f₂ ≠ 0 ∧ w.ord f₂ + D w = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace.solution
