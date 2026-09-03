import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem

set_option autoImplicit false

universe u v

theorem MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    {τ : Type v} [Fintype τ] (M : ℕ) (H : MvPowerSeries τ 𝓞)
    (hH : ∀ (μ : τ →₀ ℕ) (t : τ), ((μ t : ℕ) : 𝓞) * MvPowerSeries.coeff μ H ∈ Ideal.span {(p : 𝓞) ^ (M - 1)}) :
    ∃ ℓ : WittVector p (MvPowerSeries τ 𝓞), ∀ n : ℕ, n < M → ∀ μ' : τ →₀ ℕ,
      MvPowerSeries.coeff μ' (WittVector.ghostComponent n ℓ) = MvPowerSeries.coeff (p ^ (M - 1 - n) • μ') H := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem.solution
