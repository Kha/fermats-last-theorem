import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero

universe u v w
theorem MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero {σ : Type u} {R : Type v} [Finite σ] [CommRing R] (k : ℕ) (φ : MvPowerSeries σ R) (hφ : ∀ m : σ →₀ ℕ, m.degree < k → MvPowerSeries.coeff m φ = 0) : φ ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ k := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero.solution
