import Definitions.Def_ModularCurve_UVCrossingChart
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_chartHom_C

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) (w : W) :
    chartHom π (PowerSeries.C w) = const π w :=
  by
  rw [chartHom_apply, PowerSeries.subst_C]
  rfl
