import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false
theorem MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    ∃ (d : ℕ) (b : Fin d → MvPowerSeries (Fin n) B),
      ∀ f : MvPowerSeries (Fin n) B,
        ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_basis_subst_of_finite_quotient_of_isLocalRing.solution
