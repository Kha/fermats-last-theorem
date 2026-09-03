import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename

set_option autoImplicit false

universe u v w

open scoped TensorProduct
theorem MvPowerSeries.exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename
    {S : Type u} [CommRing S] {σ : Type v} [Fintype σ] [DecidableEq σ] {ι : Type w} [Fintype ι]
    (φ : ι → MvPowerSeries σ S)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ S) ^ N ∈ Ideal.span (Set.range φ)) :
    ∃ e : (MvPowerSeries (σ ⊕ σ) S ⧸
        Ideal.span (Set.range (fun i => MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) (φ i)) ∪
          Set.range (fun i => MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) (φ i)))) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span (Set.range φ)) ⊗[S] (MvPowerSeries σ S ⧸ Ideal.span (Set.range φ)),
      ∀ f g : MvPowerSeries σ S,
        e (Ideal.Quotient.mk _ (MvPowerSeries.rename (Sum.inl : σ → σ ⊕ σ) f * MvPowerSeries.rename (Sum.inr : σ → σ ⊕ σ) g)) =
          Ideal.Quotient.mk (Ideal.span (Set.range φ)) f ⊗ₜ[S] Ideal.Quotient.mk (Ideal.span (Set.range φ)) g := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_quotient_sum_tensorProduct_quotient_apply_mk_rename_mul_rename.solution
