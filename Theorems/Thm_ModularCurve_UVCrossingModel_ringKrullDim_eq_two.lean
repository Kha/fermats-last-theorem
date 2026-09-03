import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_ringKrullDim_eq_two

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.ringKrullDim_eq_two {W : Type*} [CommRing W] [IsNoetherianRing W] [IsLocalRing W] [IsDomain W] {π : W} (hW : IsLocalRing.maximalIdeal W = Ideal.span {π}) (hπ0 : π ≠ 0) : ringKrullDim (UVCrossingModel W π) = 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_ringKrullDim_eq_two.solution
