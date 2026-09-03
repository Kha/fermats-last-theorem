import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq

set_option autoImplicit false

universe u v w x

theorem MvPowerSeries.coeff_sumElim_single_subst_add_sum_X_mul_eq
    {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {τ : Type w} {κ : Type x} [Fintype κ]
    (f : MvPowerSeries σ R) (Df : σ → MvPowerSeries σ R)
    (hDf : ∀ (i : σ) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (Df i) = ((m i + 1 : ℕ) : R) * MvPowerSeries.coeff (m + Finsupp.single i 1) f)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (m : τ →₀ ℕ) (k : κ) :
    MvPowerSeries.coeff (m.sumElim (Finsupp.single k 1))
        (MvPowerSeries.subst
          (fun i => MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (A i) +
            ∑ k' : κ, MvPowerSeries.X (Sum.inr k') *
              MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (B i k'))
          f) =
      MvPowerSeries.coeff m (∑ i : σ, B i k * MvPowerSeries.subst A (Df i)) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_coeff_sumElim_single_subst_add_sum_X_mul_eq.solution
