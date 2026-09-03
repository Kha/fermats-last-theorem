import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_powMap_injective

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.exists_powMap_injective
    {W : Type*} [CommRing W] (π : W) (e : ℕ) (he : e ≠ 0) :
    ∃ θ : UVCrossingModel W (π ^ e) →ₐ[W] UVCrossingModel W π,
      (∀ F : MvPowerSeries (Fin 2) W, θ (mk (π ^ e) F) = mk π (MvPowerSeries.expand e he F)) ∧
      Function.Injective θ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_injective.solution
