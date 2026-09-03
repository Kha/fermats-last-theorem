import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto
      (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖)
      (𝓝[>] 1) atTop := by p2m_exact_reverting @_root_.P2MW.S_NumberField_tendsto_norm_tprod_inv_one_sub_absNorm_cpow_neg_nhdsGT_one_atTop.solution
