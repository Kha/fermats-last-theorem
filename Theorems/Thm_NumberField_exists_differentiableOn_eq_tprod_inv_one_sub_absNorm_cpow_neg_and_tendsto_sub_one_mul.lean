import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L ({s : ℂ | 1 / 2 < s.re} \ {1}) ∧
      (∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ Tendsto (fun s : ℂ => (s - 1) * L s) (𝓝[≠] 1) (𝓝 κ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.solution
