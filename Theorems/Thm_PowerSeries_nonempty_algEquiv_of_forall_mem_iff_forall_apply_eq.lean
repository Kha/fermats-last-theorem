import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq

set_option autoImplicit false

theorem PowerSeries.nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (G : Type) [Group G] [Finite G]
    (σ : G →* (PowerSeries W ≃ₐ[W] PowerSeries W))
    (S : Subalgebra W (PowerSeries W)) (hS : ∀ f : PowerSeries W, f ∈ S ↔ ∀ g : G, σ g f = f) :
    Nonempty (PowerSeries W ≃ₐ[W] ↥S) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq.solution
