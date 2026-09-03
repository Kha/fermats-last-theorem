import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_subst_injective_of_finite_projective_quotient_of_X_pow_mem_span
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

theorem MvPowerSeries.subst_injective_of_finite_projective_quotient_of_X_pow_mem_span
    {B : Type} [CommRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (hproj : Module.Projective B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (H H' : MvPowerSeries (Fin n) B) (h : MvPowerSeries.subst ρ H = MvPowerSeries.subst ρ H') : H = H' := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_subst_injective_of_finite_projective_quotient_of_X_pow_mem_span.solution
