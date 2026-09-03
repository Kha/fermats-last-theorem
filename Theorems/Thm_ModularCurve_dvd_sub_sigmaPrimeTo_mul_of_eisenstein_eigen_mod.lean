import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod

open ModularCurve

theorem ModularCurve.dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod (p m : ℕ) [Fact p.Prime] (af : ℕ → ℤ) (hT : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * ℓ) + (if ℓ ∣ n then (ℓ : ℤ) * af (n / ℓ) else 0) - (1 + ℓ) * af n) (hU : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af (n * p) - af n) : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dvd_sub_sigmaPrimeTo_mul_of_eisenstein_eigen_mod.solution
