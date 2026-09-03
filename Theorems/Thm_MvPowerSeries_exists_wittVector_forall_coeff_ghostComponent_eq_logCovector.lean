import Mathlib
import P2M.Util
import P2M.Sol.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_logCovector

set_option autoImplicit false

universe u v

theorem MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_logCovector
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hfrob : ∀ c : 𝓞, c ^ p - c ∈ Ideal.span {(p : 𝓞)})
    {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * MvPowerSeries.coeff (m + Finsupp.single j 1) φi ∈
        Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (c : (Fin d →₀ ℕ) → 𝓞)
    (hc : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → c m = (p : 𝓞) ^ (N - m.degree) * MvPowerSeries.coeff m φi) ∧
      (N < m.degree → c m * (p : 𝓞) ^ (m.degree - N) = MvPowerSeries.coeff m φi ∨
        (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ MvPowerSeries.coeff m φi))) :
    ∃ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞), ∀ n < N, ∀ m' : Fin d →₀ ℕ,
      MvPowerSeries.coeff m' (WittVector.ghostComponent n ℓ) = c (p ^ (N - 1 - n) • m') := by p2m_exact_reverting @_root_.P2MW.S_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_logCovector.solution
