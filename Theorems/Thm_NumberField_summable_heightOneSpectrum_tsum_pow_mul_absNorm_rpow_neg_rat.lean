import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import P2M.Util
import P2M.Sol.S_NumberField_summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat
    (θ C : ℝ) (hθ : 1 < θ) (hC : 0 ≤ C) (k : ℕ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
        Summable (fun m : ℕ => ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ))) ∧
      Summable (fun v : HeightOneSpectrum (𝓞 ℚ) =>
        C * ∑' m : ℕ, ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat.solution
