import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_U_notMem_span_V
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_U_ne_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [Nontrivial (W ⧸ Ideal.span {π})] :
    U π ≠ V π :=
  by
  intro h
  apply ModularCurve.UVCrossingModel.U_notMem_span_V π
  rw [h]
  exact Ideal.mem_span_singleton_self _
