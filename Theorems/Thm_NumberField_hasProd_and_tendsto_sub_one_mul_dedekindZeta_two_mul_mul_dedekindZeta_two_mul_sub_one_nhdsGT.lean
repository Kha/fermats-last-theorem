import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT

set_option autoImplicit false

open Filter Topology NumberField IsDedekindDomain

theorem NumberField.hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT
    (K : Type) [Field K] [NumberField K] :
    (∀ s : ℝ, 1 < s →
      HasProd (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s : ℂ))))⁻¹ *
          (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (s : ℂ) - 1)))⁻¹)
        (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1))) ∧
    Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
        (NumberField.dedekindZeta K (2 * (s : ℂ)) * NumberField.dedekindZeta K (2 * (s : ℂ) - 1)))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (NumberField.dedekindZeta K 2 * ((NumberField.dedekindZeta_residue K / 2 : ℝ) : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_hasProd_and_tendsto_sub_one_mul_dedekindZeta_two_mul_mul_dedekindZeta_two_mul_sub_one_nhdsGT.solution
