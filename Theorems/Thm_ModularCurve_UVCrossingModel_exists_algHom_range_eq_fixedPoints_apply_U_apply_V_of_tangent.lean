import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.UVCrossingModel~exists_unit_eigen_of_tangent"

theorem ModularCurve.UVCrossingModel.exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] [IsAdicComplete (IsLocalRing.maximalIdeal Ô) Ô]
    (π : Ô) (hπu : ¬IsUnit π) (hπ : π ∈ nonZeroDivisors Ô)
    (hnil : ∃ k : ℕ, IsLocalRing.maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π)]
    (e : ℕ) (he : IsUnit ((e : ℕ) : Ô)) (ζ ζ' : Ô) (hζ : ζ * ζ' = 1) (hζe : ζ ^ e = 1)
    (hreg : ∀ m : ℕ, 0 < m → m < e → ζ ^ m - 1 ∈ nonZeroDivisors Ô)
    (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (hord : ∀ z, σ^[e] z = z)
    (htanU : σ (U π) - const π ζ * U π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2)
    (htanV : σ (V π) - const π ζ' * V π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2) :
    ∃ (ι : UVCrossingModel Ô (π ^ e) →ₐ[Ô] UVCrossingModel Ô π) (γ : (UVCrossingModel Ô π)ˣ),
      Function.Injective ι ∧ (∀ z : UVCrossingModel Ô π, σ z = z ↔ z ∈ Set.range ι) ∧
      (γ : UVCrossingModel Ô π) - 1 ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ∧
      ι (U (π ^ e)) = ((γ : UVCrossingModel Ô π) * U π) ^ e ∧
      ι (V (π ^ e)) = ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) ^ e := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_algHom_range_eq_fixedPoints_apply_U_apply_V_of_tangent.solution
