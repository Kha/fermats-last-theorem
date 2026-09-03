import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

p2m_open "MvPowerSeries~finite_flat_exists_basis_substAlgHom_of_finite_quotient"

theorem MvPowerSeries.eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n d : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (b : Fin d → MvPowerSeries (Fin n) B)
    (β : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (MvPowerSeries (Fin n) (IsLocalRing.ResidueField B) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i))))
    (hβ : ∀ j, β j = Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i)))
      (MvPowerSeries.map (IsLocalRing.residue B) (b j)))
    (c c' : Fin d → MvPowerSeries (Fin n) B)
    (h : ∑ j, MvPowerSeries.subst ρ (c j) * b j = ∑ j, MvPowerSeries.subst ρ (c' j) * b j) : c = c' := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue.solution
