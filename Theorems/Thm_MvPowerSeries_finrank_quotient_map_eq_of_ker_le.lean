import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_finrank_quotient_map_eq_of_ker_le
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

theorem MvPowerSeries.finrank_quotient_map_eq_of_ker_le
    {B : Type} [CommRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    {κ κ' : Type} [Field κ] [Field κ'] (f : B →+* κ) (g : B →+* κ') (hfg : RingHom.ker g ≤ RingHom.ker f) :
    Module.finrank κ (MvPowerSeries (Fin n) κ ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map f (ρ i))) =
      Module.finrank κ' (MvPowerSeries (Fin n) κ' ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map g (ρ i))) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_finrank_quotient_map_eq_of_ker_le.solution
