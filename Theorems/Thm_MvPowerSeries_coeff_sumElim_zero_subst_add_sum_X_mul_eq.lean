import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq

set_option autoImplicit false

universe u v w x

theorem MvPowerSeries.coeff_sumElim_zero_subst_add_sum_X_mul_eq
    {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {τ : Type w} {κ : Type x} [Fintype κ]
    (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) (m : τ →₀ ℕ) :
    MvPowerSeries.coeff (m.sumElim 0)
        (MvPowerSeries.subst
          (fun i => MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (A i) +
            ∑ k' : κ, MvPowerSeries.X (Sum.inr k') *
              MvPowerSeries.subst (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (τ ⊕ κ) R)) (B i k'))
          f) =
      MvPowerSeries.coeff m (MvPowerSeries.subst A f) := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_coeff_sumElim_zero_subst_add_sum_X_mul_eq.solution
