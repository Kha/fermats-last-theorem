import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ)
    (hab : ∀ v, (‖a v‖ = 1 ∧ b v = a v ^ 2) ∨ (a v = 0 ∧ ‖b v‖ ≤ 1))
    (hζ : ∃ C δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C / (σ - 1))
    (ha : ∃ U ∈ 𝓝 (1 : ℂ), ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      ∀ s ∈ U, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
    (hb : ∃ B δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - b v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ B) :
    ¬ Tendsto
        (fun σ : ℝ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - a v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹)
        (𝓝[>] 1) (𝓝 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.solution
