import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

theorem MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le
    {σ : Type w} [Finite σ] {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    {ι : Type t} (φ : ι → MvPowerSeries σ R) (N : ℕ)
    (hN : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ N ≤
      Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_pow_span_X_le.solution
