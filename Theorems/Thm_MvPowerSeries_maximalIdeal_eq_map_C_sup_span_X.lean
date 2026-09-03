import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_maximalIdeal_eq_map_C_sup_span_X

universe u v w
theorem MvPowerSeries.maximalIdeal_eq_map_C_sup_span_X {σ : Type u} {R : Type v} [Finite σ] [CommRing R] [IsLocalRing R] : IsLocalRing.maximalIdeal (MvPowerSeries σ R) = (IsLocalRing.maximalIdeal R).map (MvPowerSeries.C (σ := σ) (R := R)) ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_maximalIdeal_eq_map_C_sup_span_X.solution
