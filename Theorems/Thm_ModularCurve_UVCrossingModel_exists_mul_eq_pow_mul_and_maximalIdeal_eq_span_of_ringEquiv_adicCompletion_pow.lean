import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)

    (𝔭₁ 𝔭₂ : Ideal O) [𝔭₁.IsPrime] [𝔭₂.IsPrime] (h₁₂ : 𝔭₁ ≠ 𝔭₂)
    (ht₁ : t ∈ 𝔭₁) (ht₂ : t ∈ 𝔭₂) (h₁ : 𝔭₁ ≠ maximalIdeal O) (h₂ : 𝔭₂ ≠ maximalIdeal O) :
    ∃ (xn yn u : O) (γ γ' : UVCrossingModel W (π ^ w)),
      IsUnit u ∧ IsUnit γ ∧ IsUnit γ' ∧
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) xn) = γ * U (π ^ w) ∧
      ι (algebraMap O (AdicCompletion (maximalIdeal O) O) yn) = γ' * V (π ^ w) ∧
      xn * yn = t ^ w * u ∧
      maximalIdeal O = Ideal.span {xn, yn, t} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow.solution
