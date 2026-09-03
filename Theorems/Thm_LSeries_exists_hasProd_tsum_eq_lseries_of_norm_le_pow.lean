import Mathlib.NumberTheory.LSeries.Convergence
import P2M.Util
import P2M.Sol.S_LSeries_exists_hasProd_tsum_eq_lseries_of_norm_le_pow

set_option autoImplicit false

open scoped ComplexOrder

theorem LSeries.exists_hasProd_tsum_eq_lseries_of_norm_le_pow
    {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)
    (E : ι → ℕ → ℂ) (hE0 : ∀ i : ι, E i 0 = 1) (A : ℝ)
    (hEA : ∀ (i : ι) (k : ℕ), ‖E i k‖ ≤ (((N i : ℝ) ^ k) ^ A)) :
    ∃ c : ℕ → ℂ,
      (∀ (i : ι) (k : ℕ), c (N i ^ k) = E i k) ∧
      ((∀ (i : ι) (k : ℕ), 0 ≤ E i k) → 0 ≤ c) ∧
      LSeries.abscissaOfAbsConv c ≤ ((A + 1 : ℝ) : EReal) ∧
      ∀ s : ℂ, A + 1 < s.re →
        HasProd (fun i : ι => ∑' k : ℕ, E i k * (((N i : ℕ) : ℂ) ^ (-s)) ^ k) (LSeries c s) := by p2m_exact_reverting @_root_.P2MW.S_LSeries_exists_hasProd_tsum_eq_lseries_of_norm_le_pow.solution
