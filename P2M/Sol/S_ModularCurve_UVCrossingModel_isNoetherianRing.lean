import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_isNoetherianRing

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] [IsNoetherianRing W] (π : W) :
    IsNoetherianRing (UVCrossingModel W π) :=
  by
  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) W) := MvPowerSeries.isNoetherianRing_of_finite
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin 2) W) (UVCrossingModel W π)
    (UVCrossingModel.mk π) (UVCrossingModel.mk_surjective π)
