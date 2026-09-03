import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT

set_option autoImplicit false

open Filter Topology NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ s : ℝ, 1 < s →
      0 < (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) ∧
    (∀ s : ℝ, 1 < s →
      Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 K)) =>
          ∏ v ∈ T \ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s)))⁻¹ *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s))⁻¹))
        atTop
        (𝓝 (ENNReal.ofReal
              ((NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))))) ∧
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) *
        (ENNReal.ofReal
            ((NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)).re) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 * s))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - 2 * s)))))
      (𝓝[>] (1 : ℝ))
      (𝓝 (ENNReal.ofReal ((NumberField.dedekindZeta K 2).re * (NumberField.dedekindZeta_residue K / 2)) *
          ∏ v ∈ S, ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ))) *
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(1 : ℝ)))))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_tendsto_prod_sdiff_inv_one_sub_absNorm_rpow_atTop_and_tendsto_sub_one_mul_re_dedekindZeta_two_mul_nhdsGT.solution
