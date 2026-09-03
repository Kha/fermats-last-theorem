import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_maximalIdeal_eq_comap_constantCoeff

universe u v w
theorem MvPowerSeries.maximalIdeal_eq_comap_constantCoeff {σ : Type u} {R : Type v} [CommRing R] [IsLocalRing R] : IsLocalRing.maximalIdeal (MvPowerSeries σ R) = (IsLocalRing.maximalIdeal R).comap (MvPowerSeries.constantCoeff (σ := σ) (R := R)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_maximalIdeal_eq_comap_constantCoeff.solution
