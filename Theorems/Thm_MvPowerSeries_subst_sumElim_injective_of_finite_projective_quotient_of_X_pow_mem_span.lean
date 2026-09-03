import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span
    {B : Type} [CommRing B] [IsNoetherianRing B] {n : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B) (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (hproj : Module.Projective B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
(∀ H H' : MvPowerSeries (Fin n ⊕ Fin n) B,
      MvPowerSeries.subst (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))) H =
      MvPowerSeries.subst (Sum.elim
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))
          (fun j => MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) B)) (ρ j))) H' → H = H') := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_subst_sumElim_injective_of_finite_projective_quotient_of_X_pow_mem_span.solution
