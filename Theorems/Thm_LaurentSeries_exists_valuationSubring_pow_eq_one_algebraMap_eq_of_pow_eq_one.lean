import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one

set_option autoImplicit false

theorem LaurentSeries.exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
    {k₀ : Type*} [Field k₀] (K : IntermediateField k₀ (LaurentSeries k₀))
    (A₀ : ValuationSubring k₀) [Algebra A₀ K] [IsScalarTower A₀ k₀ K]
    {n : ℕ} (hn : n ≠ 0) (ζ : K) (hζ : ζ ^ n = 1) :
    ∃ a : A₀, a ^ n = 1 ∧ algebraMap A₀ K a = ζ := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one.solution
