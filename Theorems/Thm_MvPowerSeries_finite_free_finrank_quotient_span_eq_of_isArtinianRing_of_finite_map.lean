import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u v

theorem MvPowerSeries.finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map
    {A : Type u} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    {k : Type v} [Field k] (res : A →+* k) (hres : Function.Surjective res)
    {d : ℕ} (f : Fin d → MvPowerSeries (Fin d) A) (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map res (f i)))) :
    Module.Finite A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range f)) ∧
    Module.Free A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range f)) ∧
    Module.finrank A (MvPowerSeries (Fin d) A ⧸ Ideal.span (Set.range f)) =
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map res (f i))) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_finite_free_finrank_quotient_span_eq_of_isArtinianRing_of_finite_map.solution
