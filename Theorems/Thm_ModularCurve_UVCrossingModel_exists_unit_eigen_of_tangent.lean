import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_unit_eigen_of_tangent
    {Ô : Type*} [CommRing Ô] [IsLocalRing Ô] (π : Ô) (hπu : ¬IsUnit π) (hπ : π ∈ nonZeroDivisors Ô)
    (hnil : ∃ k : ℕ, IsLocalRing.maximalIdeal Ô ^ k ≤ Ideal.span {π})
    [IsLocalRing (UVCrossingModel Ô π)]
    [IsAdicComplete (IsLocalRing.maximalIdeal (UVCrossingModel Ô π)) (UVCrossingModel Ô π)]
    (e : ℕ) (he : IsUnit ((e : ℕ) : Ô)) (ζ ζ' : Ô) (hζ : ζ * ζ' = 1) (hζe : ζ ^ e = 1)
    (σ : UVCrossingModel Ô π ≃ₐ[Ô] UVCrossingModel Ô π) (hord : ∀ z, σ^[e] z = z)
    (htanU : σ (U π) - const π ζ * U π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2)
    (htanV : σ (V π) - const π ζ' * V π ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ^ 2) :
    ∃ γ : (UVCrossingModel Ô π)ˣ, (γ : UVCrossingModel Ô π) - 1 ∈ IsLocalRing.maximalIdeal (UVCrossingModel Ô π) ∧
      σ ((γ : UVCrossingModel Ô π) * U π) = const π ζ * ((γ : UVCrossingModel Ô π) * U π) ∧
      σ ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) = const π ζ' * ((↑γ⁻¹ : UVCrossingModel Ô π) * V π) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_unit_eigen_of_tangent.solution
