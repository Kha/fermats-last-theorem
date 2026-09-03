import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PowerSeries.Basic
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ

universe u v w
theorem MvPowerSeries.exists_algEquiv_powerSeries_fin_succ (R : Type u) [CommSemiring R] (n : ℕ) : ∃ e : MvPowerSeries (Fin (n + 1)) R ≃ₐ[R] PowerSeries (MvPowerSeries (Fin n) R), e (MvPowerSeries.X 0) = PowerSeries.X ∧ ∀ i : Fin n, e (MvPowerSeries.X i.succ) = PowerSeries.C (MvPowerSeries.X i) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_powerSeries_fin_succ.solution
