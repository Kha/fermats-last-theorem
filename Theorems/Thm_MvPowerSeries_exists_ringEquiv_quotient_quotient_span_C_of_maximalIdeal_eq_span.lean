import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span

set_option autoImplicit false

universe u v

open MvPowerSeries

theorem MvPowerSeries.exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span
    {W : Type u} [CommRing W] [IsLocalRing W] (π : W) (hπ : IsLocalRing.maximalIdeal W = Ideal.span {π})
    {σ : Type v} (g : MvPowerSeries σ W) :
    ∃ e : ((MvPowerSeries σ W ⧸ Ideal.span {g}) ⧸
          Ideal.span {Ideal.Quotient.mk (Ideal.span {g}) (C π)}) ≃+*
        (MvPowerSeries σ (IsLocalRing.ResidueField W) ⧸ Ideal.span {MvPowerSeries.map (IsLocalRing.residue W) g}),
      ∀ p : MvPowerSeries σ W,
        e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {g}) p)) =
          Ideal.Quotient.mk _ (MvPowerSeries.map (IsLocalRing.residue W) p) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_ringEquiv_quotient_quotient_span_C_of_maximalIdeal_eq_span.solution
