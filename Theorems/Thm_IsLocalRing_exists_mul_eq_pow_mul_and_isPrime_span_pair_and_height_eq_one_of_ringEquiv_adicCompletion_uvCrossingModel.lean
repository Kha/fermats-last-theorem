import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem IsLocalRing.exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsLocalRing B]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal B) B ≃+* UVCrossingModel W (π ^ E))
    (t x y : B)
    (ht : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) t) = const (π ^ E) π)
    (γU γV : (UVCrossingModel W (π ^ E))ˣ)
    (hx : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) x) = (γU : UVCrossingModel W (π ^ E)) * U (π ^ E))
    (hy : ι (algebraMap B (AdicCompletion (maximalIdeal B) B) y) = (γV : UVCrossingModel W (π ^ E)) * V (π ^ E)) :
    (∃ u : B, IsUnit u ∧ x * y = t ^ E * u) ∧
    (Ideal.span {t, y}).IsPrime ∧ x ∉ Ideal.span {t, y} ∧
    (∀ 𝔮 : Ideal B, 𝔮.IsPrime → t ∈ 𝔮 → x ∉ 𝔮 → 𝔮 ≠ maximalIdeal B → 𝔮 = Ideal.span {t, y}) ∧
    (Ideal.span {t, y}).height = 1 := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_mul_eq_pow_mul_and_isPrime_span_pair_and_height_eq_one_of_ringEquiv_adicCompletion_uvCrossingModel.solution
