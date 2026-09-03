import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_powMap_range_eq_fixedPoints

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_powMap_range_eq_fixedPoints
    {W : Type*} [CommRing W] (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (e : ℕ) (he : e ≠ 0)
    (ζ ζ' : W) (hζ : ζ ^ e = 1) (hζζ' : ζ * ζ' = 1)
    (hreg : ∀ m : ℕ, 0 < m → m < e → ζ ^ m - 1 ∈ nonZeroDivisors W) :
    ∃ (θ : UVCrossingModel W (π ^ e) →ₐ[W] UVCrossingModel W π)
      (δ : UVCrossingModel W π ≃ₐ[W] UVCrossingModel W π),
      (∀ F : MvPowerSeries (Fin 2) W, θ (mk (π ^ e) F) = mk π (MvPowerSeries.expand e he F)) ∧
      Function.Injective θ ∧
      (∀ F : MvPowerSeries (Fin 2) W, δ (mk π F) = mk π (MvPowerSeries.rescale ![ζ, ζ'] F)) ∧
      ∀ z : UVCrossingModel W π, δ z = z ↔ z ∈ Set.range θ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_range_eq_fixedPoints.solution
