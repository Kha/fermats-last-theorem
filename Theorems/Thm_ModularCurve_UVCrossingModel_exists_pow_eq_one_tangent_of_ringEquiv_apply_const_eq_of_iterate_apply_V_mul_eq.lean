import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq

set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve ModularCurve.UVCrossingModel~exists_ringEquiv_quotient_span_U_powerSeries~U_mul_V~exists_sub_const_mem_maximalIdeal~exists_isUnit_apply_V_eq_mul_V_of_ringEquiv_apply_const_eq_of_apply_U_not_mem_span~V_mem_nonZeroDivisors"

theorem ModularCurve.UVCrossingModel.exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    [IsLocalRing (UVCrossingModel W (ϖ ^ e))]
    (θ : UVCrossingModel W (ϖ ^ e) ≃+* UVCrossingModel W (ϖ ^ e))
    (hθc : ∀ w : W, θ (const (ϖ ^ e) w) = const (ϖ ^ e) w)
    (hθU : θ (U (ϖ ^ e)) ∉ Ideal.span {V (ϖ ^ e), const (ϖ ^ e) ϖ})
    (n : ℕ) (hn : 1 ≤ n) (hnW : IsUnit ((n : ℕ) : W))
    (β : UVCrossingModel W (ϖ ^ e)) (hβ : IsUnit β)

    (hfix : (θ ^ n) (V (ϖ ^ e) * β) = V (ϖ ^ e) * β)

    (c : ℕ → W)
    (hread : ∀ k : ℕ, 0 < k → k < n →
      (θ ^ k) (V (ϖ ^ e) * β) - const (ϖ ^ e) (c k) * (V (ϖ ^ e) * β) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2)
    (hfaith : ∀ k : ℕ, 0 < k → k < n → c k - 1 ∉ maximalIdeal W) :
    ∃ ζ ζ' : W, ζ ^ n = 1 ∧ (∀ k : ℕ, 0 < k → k < n → IsUnit (ζ ^ k - 1)) ∧ ζ * ζ' = 1 ∧
      θ (U (ϖ ^ e)) - const (ϖ ^ e) ζ * U (ϖ ^ e) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 ∧
      θ (V (ϖ ^ e)) - const (ϖ ^ e) ζ' * V (ϖ ^ e) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 ∧
      (∀ c' : W, θ (V (ϖ ^ e) * β) - const (ϖ ^ e) c' * (V (ϖ ^ e) * β) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 →
        ζ' - c' ∈ maximalIdeal W) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq.solution
