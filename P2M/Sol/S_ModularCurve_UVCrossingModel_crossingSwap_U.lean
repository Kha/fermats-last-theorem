import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_crossingSwap_U

open ModularCurve ModularCurve.UVCrossingModel

theorem solution {W : Type*} [CommRing W] (π : W) :
    crossingSwap π (U π) = V π :=
  by
  have h : crossingSwap π (UVCrossingModel.mk π (MvPowerSeries.X 0)) =
      UVCrossingModel.mk π (uvSwapEquiv (MvPowerSeries.X 0)) := crossingSwap_mk π _
  rw [uvSwapEquiv_X_zero] at h
  exact h
