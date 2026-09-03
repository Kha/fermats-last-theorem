import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvPowerSeries.finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq
    {k : Type u} [Field k] {d : ℕ} (T : Finset (Fin d)) (q : ℕ) (hq : 0 < q)
    (g : Fin d → MvPowerSeries (Fin d) k) (hg : ∀ i, (g i).constantCoeff = 0) :
    (Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i =>
        subst (fun j => if j ∈ T then (X j : MvPowerSeries (Fin d) k) else X j ^ q) (g i))) ↔
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) ∧
    Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i =>
        subst (fun j => if j ∈ T then (X j : MvPowerSeries (Fin d) k) else X j ^ q) (g i))) =
      q ^ (d - T.card) *
        Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq.solution
