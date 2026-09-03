import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_Smooth_fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime

set_option autoImplicit false

open IsLocalRing

theorem Algebra.Smooth.fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    {F₀ : Type} [Field F₀] [Algebra A₀ F₀]
    (B : Subalgebra A₀ F₀) [Algebra.Smooth A₀ ↥B]
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)
    (hprime : (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).IsPrime)
    (hdim1 : Ring.KrullDimLE 1 (↥B ⧸ Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀))) :
    B.FG ∧
    (∀ x : F₀, IsIntegral ↥B x → x ∈ B) ∧
    (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
    (∀ (𝔪 : Ideal ↥B) [𝔪.IsPrime], (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_fg_and_isIntegral_mem_and_minimalPrimes_and_formallySmooth_localizationAtPrime.solution
