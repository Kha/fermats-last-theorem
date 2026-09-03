import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent

set_option autoImplicit false

universe u

theorem MvPowerSeries.free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent
    (R : Type u) [CommRing R] [Nontrivial R] (g : ℕ) (N : Fin g → ℕ) (c : Fin g → R)
    (hc : ∀ i, IsNilpotent (c i)) :
    Module.Free R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g =>
          MvPowerSeries.C (c i) * MvPowerSeries.X i + (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.Finite R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g =>
          MvPowerSeries.C (c i) * MvPowerSeries.X i + (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i)) ∧
      Module.finrank R (MvPowerSeries (Fin g) R ⧸
        Ideal.span (Set.range fun i : Fin g =>
          MvPowerSeries.C (c i) * MvPowerSeries.X i + (MvPowerSeries.X i : MvPowerSeries (Fin g) R) ^ N i))
          = ∏ i, N i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_free_and_finite_and_finrank_quotient_span_range_C_mul_X_add_X_pow_of_isNilpotent.solution
