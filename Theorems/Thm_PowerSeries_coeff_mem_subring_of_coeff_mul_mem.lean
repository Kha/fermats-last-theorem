import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem

set_option autoImplicit false

theorem PowerSeries.coeff_mem_subring_of_coeff_mul_mem {K : Type*} [CommRing K] (R : Subring K)
    (P U : PowerSeries K) (m₀ L : ℕ)
    (hU₀ : ∀ n : ℕ, n < m₀ → PowerSeries.coeff n U = 0)
    (hU₁ : ∃ v ∈ R, v * PowerSeries.coeff m₀ U = 1)
    (hU : ∀ n : ℕ, PowerSeries.coeff n U ∈ R)
    (hPU : ∀ n : ℕ, n < L → PowerSeries.coeff n (P * U) ∈ R)
    (n : ℕ) (hn : n + m₀ < L) :
    PowerSeries.coeff n P ∈ R := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_coeff_mem_subring_of_coeff_mul_mem.solution
