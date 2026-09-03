import Mathlib
import P2M.Util
import P2M.Sol.S_NumberField_tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one

set_option autoImplicit false

open IsDedekindDomain NumberField

open scoped Classical in

theorem NumberField.tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one
    (F : Type) [Field F] [NumberField F]
    (S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))) (_h : S₁ ⊆ S₂)
    (z : HeightOneSpectrum (𝓞 F) → ℂ) (_hz : ∀ v, ‖z v‖ ≤ 1) (s : ℂ) (_hs : 1 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂},
        (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      * (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₁},
          (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
      = ∏ v ∈ S₂ \ S₁, (1 - z v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one.solution
