import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range

set_option autoImplicit false

open IsLocalRing
theorem IsLocalRing.existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
    {B : Type} [CommRing B] [IsLocalRing B]
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    {r : ℕ} (bV : Module.Basis (Fin r) (ResidueField B) V)
    {τ : Type} (Δ : MvPowerSeries τ B) (hΔ : ∀ n, MvPowerSeries.coeff n Δ ∈ LinearMap.range ι) :
    (∃! z : Fin r → MvPowerSeries τ (ResidueField B),
        ∀ zl : Fin r → MvPowerSeries τ B, (∀ i, MvPowerSeries.map (residue B) (zl i) = z i) → Δ = ∑ i, ι (bV i) • zl i) ∧
    (∀ z : Fin r → MvPowerSeries τ (ResidueField B), ∃ zl : Fin r → MvPowerSeries τ B, ∀ i, MvPowerSeries.map (residue B) (zl i) = z i) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range.solution
