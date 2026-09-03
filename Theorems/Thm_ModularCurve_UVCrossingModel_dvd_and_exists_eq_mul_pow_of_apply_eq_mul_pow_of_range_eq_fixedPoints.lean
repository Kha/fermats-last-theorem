import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (m : ℕ) (hm : 1 ≤ m)
    [IsLocalRing (UVCrossingModel W (π ^ m))]
    [IsAdicComplete (maximalIdeal (UVCrossingModel W (π ^ m))) (UVCrossingModel W (π ^ m))]
    (n : ℕ) (hn : 1 ≤ n) (hnu : IsUnit ((n : ℕ) : W)) (ζ ζ' : W) (hζ : ζ * ζ' = 1) (hζn : ζ ^ n = 1)
    (hζprim : ∀ j : ℕ, 0 < j → j < n → IsUnit (ζ ^ j - 1))
    (θ : UVCrossingModel W (π ^ m) ≃ₐ[W] UVCrossingModel W (π ^ m)) (hord : ∀ z, θ^[n] z = z)
    (htanU : θ (U (π ^ m)) - const (π ^ m) ζ * U (π ^ m) ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ^ 2)
    (htanV : θ (V (π ^ m)) - const (π ^ m) ζ' * V (π ^ m) ∈ maximalIdeal (UVCrossingModel W (π ^ m)) ^ 2)
    (ψ : UVCrossingModel W (π ^ (m * n)) →+* UVCrossingModel W (π ^ m)) (hψinj : Function.Injective ψ)
    (hψc : ∀ w : W, ψ (const (π ^ (m * n)) w) = const (π ^ m) w)
    (γ γ' : (UVCrossingModel W (π ^ m))ˣ)
    (hψU : ψ (U (π ^ (m * n))) = ((γ : UVCrossingModel W (π ^ m)) * U (π ^ m)) ^ n)
    (hψV : ψ (V (π ^ (m * n))) = ((γ' : UVCrossingModel W (π ^ m)) * V (π ^ m)) ^ n)
    (hψrange : ∀ z : UVCrossingModel W (π ^ m), z ∈ Set.range ψ ↔ θ z = z) :
    (∀ (z : UVCrossingModel W (π ^ (m * n))) (e : ℕ) (w : (UVCrossingModel W (π ^ m))ˣ),
      ψ z = (w : UVCrossingModel W (π ^ m)) * V (π ^ m) ^ e →
        n ∣ e ∧ ∃ w' : (UVCrossingModel W (π ^ (m * n)))ˣ, z = (w' : UVCrossingModel W (π ^ (m * n))) * V (π ^ (m * n)) ^ (e / n)) ∧
    (∀ (z : UVCrossingModel W (π ^ (m * n))) (e : ℕ) (w : (UVCrossingModel W (π ^ m))ˣ),
      ψ z = (w : UVCrossingModel W (π ^ m)) * U (π ^ m) ^ e →
        n ∣ e ∧ ∃ w' : (UVCrossingModel W (π ^ (m * n)))ˣ, z = (w' : UVCrossingModel W (π ^ (m * n))) * U (π ^ (m * n)) ^ (e / n)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_dvd_and_exists_eq_mul_pow_of_apply_eq_mul_pow_of_range_eq_fixedPoints.solution
