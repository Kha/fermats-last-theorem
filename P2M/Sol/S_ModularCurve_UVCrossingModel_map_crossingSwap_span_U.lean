import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_crossingSwap_U
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_map_crossingSwap_span_U

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) :
    Ideal.map (crossingSwap π) (Ideal.span {U π}) = Ideal.span {V π} :=
  by
  rw [Ideal.map_span, Set.image_singleton, ModularCurve.UVCrossingModel.crossingSwap_U]
