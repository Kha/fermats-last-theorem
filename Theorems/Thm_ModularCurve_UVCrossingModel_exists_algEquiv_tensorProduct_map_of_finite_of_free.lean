import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem ModularCurve.UVCrossingModel.exists_algEquiv_tensorProduct_map_of_finite_of_free
    (W W' : Type u) [CommRing W] [CommRing W'] [Algebra W W'] [Module.Finite W W'] [Module.Free W W']
    (a : W) :
    ∃ e : ModularCurve.UVCrossingModel W a ⊗[W] W' ≃ₐ[W]
        ModularCurve.UVCrossingModel W' (algebraMap W W' a),
      (∀ (f : MvPowerSeries (Fin 2) W) (w' : W'),
        e (ModularCurve.UVCrossingModel.mk a f ⊗ₜ[W] w') =
          ModularCurve.UVCrossingModel.const (algebraMap W W' a) w' *
            ModularCurve.UVCrossingModel.mk (algebraMap W W' a) (MvPowerSeries.map (algebraMap W W') f)) ∧
      e (ModularCurve.UVCrossingModel.U a ⊗ₜ[W] 1) = ModularCurve.UVCrossingModel.U (algebraMap W W' a) ∧
      e (ModularCurve.UVCrossingModel.V a ⊗ₜ[W] 1) = ModularCurve.UVCrossingModel.V (algebraMap W W' a) ∧
      ∀ w : W, e (ModularCurve.UVCrossingModel.const a w ⊗ₜ[W] 1) =
        ModularCurve.UVCrossingModel.const (algebraMap W W' a) (algebraMap W W' w) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_algEquiv_tensorProduct_map_of_finite_of_free.solution
