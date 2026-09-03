import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import P2M.Util
namespace P2MW.S_ModularCurve_UVCrossingModel_isDomain_quotient_span_V

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] :
    IsDomain (UVCrossingModel W π ⧸ Ideal.span {V π}) :=
  by
  obtain ⟨e, -, -, -⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries π
  exact MulEquiv.isDomain (PowerSeries (W ⧸ Ideal.span {π})) e.toMulEquiv
