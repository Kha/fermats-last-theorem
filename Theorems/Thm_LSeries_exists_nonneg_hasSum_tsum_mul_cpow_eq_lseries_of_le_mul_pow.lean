import Mathlib.NumberTheory.LSeries.Convergence
import P2M.Util
import P2M.Sol.S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow

set_option autoImplicit false

open scoped ComplexOrder

theorem LSeries.exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow
    {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)
    (c : ι → ℕ → ℝ) (hc0 : ∀ i : ι, c i 0 = 0) (hc : ∀ (i : ι) (m : ℕ), 0 ≤ c i m)
    (B : ℝ) (hcB : ∀ (i : ι) (m : ℕ), c i m ≤ B * (N i : ℝ) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      (∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m) ∧
      (∀ n : ℕ, d n ≠ 0 → ∃ (i : ι) (m : ℕ), 0 < m ∧ N i ^ m = n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      (∀ s : ℂ, 2 < s.re →
        (∀ i : ι, Summable (fun m : ℕ => (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)) ∧
        HasSum (fun i : ι => ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s)) ∧
      ∀ σ : ℝ, LSeriesSummable (fun n => (d n : ℂ)) σ →
        Summable (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) ∧
        ∑' i : ι, c i 1 * (N i : ℝ) ^ (-σ) ≤ (LSeries (fun n => (d n : ℂ)) σ).re := by p2m_exact_reverting @_root_.P2MW.S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow.solution
