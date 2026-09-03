import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul
attribute [-instance] instTopologicallyFGOfFiniteType

universe u

theorem MvPowerSeries.finite_and_finrank_quotient_span_range_subst_eq_mul
    {k : Type u} [Field k] {d : ℕ} (f g : Fin d → MvPowerSeries (Fin d) k)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hffin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range f)))
    (hgfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :
    Module.Finite k
        (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i => MvPowerSeries.subst g (f i))) ∧
      Module.finrank k
          (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i => MvPowerSeries.subst g (f i))) =
        Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range f)) *
          Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_eq_mul.solution
