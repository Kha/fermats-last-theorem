import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open MvPowerSeries hiding finite_flat_exists_basis_substAlgHom_of_finite_quotient exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem exists_basis_subst_of_finite_quotient_of_isLocalRing

theorem MvPowerSeries.free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    Module.Free B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)) ∧
      ∀ (κ : Type) [Field κ] (f : B →+* κ),
        Module.finrank κ (MvPowerSeries (Fin n) κ ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map f (ρ i))) =
          Module.finrank B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_free_quotient_and_finrank_quotient_map_eq_of_finite_of_isLocalRing.solution
