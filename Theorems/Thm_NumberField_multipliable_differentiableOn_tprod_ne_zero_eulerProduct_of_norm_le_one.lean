import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    (M : Type) [Field M] [NumberField M] (S : Finset (HeightOneSpectrum (𝓞 M)))
    (z : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) :
    (∀ s : ℂ, 1 < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} =>
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) ∧
      DifferentiableOn ℂ
        (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
        {s : ℂ | 1 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one.solution
