import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
attribute [-instance] instTopologicallyFGOfFiniteType

universe u

theorem MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient
    {k : Type u} [Field k] {d : ℕ} (g : Fin d → MvPowerSeries (Fin d) k)
    (hg : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (hfin : Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) :
    RingHom.Finite (A := MvPowerSeries (Fin d) k) (B := MvPowerSeries (Fin d) k)
      (MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)).toRingHom ∧
    RingHom.Flat (R := MvPowerSeries (Fin d) k) (S := MvPowerSeries (Fin d) k)
      (MvPowerSeries.substAlgHom (R := k) (MvPowerSeries.hasSubst_of_constantCoeff_zero hg)).toRingHom ∧
    ∃ b : Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) → MvPowerSeries (Fin d) k,
      ∀ x : MvPowerSeries (Fin d) k,
        ∃! c : Fin (Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range g))) →
            MvPowerSeries (Fin d) k,
          x = ∑ i, MvPowerSeries.subst g (c i) * b i := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient.solution
