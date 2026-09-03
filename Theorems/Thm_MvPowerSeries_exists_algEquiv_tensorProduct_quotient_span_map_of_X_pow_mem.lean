import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem

set_option autoImplicit false

open scoped TensorProduct

theorem MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
    {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S]
    {σ : Type} [Fintype σ] {ι : Type} (φ : ι → MvPowerSeries σ R)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem.solution
