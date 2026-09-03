import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq

set_option autoImplicit false

universe u v

theorem MvPowerSeries.le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {τ : Type v} [Fintype τ] (M L : ℕ) (H : MvPowerSeries τ 𝓞)
    (hL : ∀ μ : τ →₀ ℕ, MvPowerSeries.coeff μ H ≠ 0 → L ≤ μ.degree)
    (ℓ : WittVector p (MvPowerSeries τ 𝓞))
    (hℓ : ∀ n : ℕ, n < M → ∀ μ' : τ →₀ ℕ,
      MvPowerSeries.coeff μ' (WittVector.ghostComponent n ℓ) = MvPowerSeries.coeff (p ^ (M - 1 - n) • μ') H)
    (j : ℕ) (hj : j < M) (μ' : τ →₀ ℕ) (hμ' : MvPowerSeries.coeff μ' (ℓ.coeff j) ≠ 0) :
    L ≤ p ^ (M - 1 - j) * μ'.degree := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq.solution
