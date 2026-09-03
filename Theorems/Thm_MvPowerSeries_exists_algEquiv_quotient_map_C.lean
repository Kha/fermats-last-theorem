import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algEquiv_quotient_map_C

universe u v w
theorem MvPowerSeries.exists_algEquiv_quotient_map_C {σ : Type u} {R : Type v} [CommRing R] (I : Ideal R) (hI : I.FG) : ∃ e : (MvPowerSeries σ R ⧸ I.map (MvPowerSeries.C (σ := σ) (R := R))) ≃ₐ[R] MvPowerSeries σ (R ⧸ I), ∀ p : MvPowerSeries σ R, e (Ideal.Quotient.mk (I.map (MvPowerSeries.C (σ := σ) (R := R))) p) = MvPowerSeries.map (Ideal.Quotient.mk I) p := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_quotient_map_C.solution
