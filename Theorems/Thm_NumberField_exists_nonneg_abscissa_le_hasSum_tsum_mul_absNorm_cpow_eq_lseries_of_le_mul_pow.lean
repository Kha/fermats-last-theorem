import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import P2M.Util
import P2M.Sol.S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
    (K : Type) [Field K] [NumberField K]
    (c : HeightOneSpectrum (𝓞 K) → ℕ → ℝ)
    (hc0 : ∀ v : HeightOneSpectrum (𝓞 K), c v 0 = 0)
    (hc : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ), 0 ≤ c v m)
    (B : ℝ) (hcB : ∀ (v : HeightOneSpectrum (𝓞 K)) (m : ℕ),
      c v m ≤ B * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      ∀ s : ℂ, 2 < s.re →
        (∀ v : HeightOneSpectrum (𝓞 K),
          Summable (fun m : ℕ => (c v m : ℂ) * ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) ^ m)) ∧
        HasSum (fun v : HeightOneSpectrum (𝓞 K) =>
            ∑' m : ℕ, (c v m : ℂ) * ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow.solution
