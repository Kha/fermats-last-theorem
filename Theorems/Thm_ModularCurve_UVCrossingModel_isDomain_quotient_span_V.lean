import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isDomain_quotient_span_V

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.isDomain_quotient_span_V {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] : IsDomain (UVCrossingModel W π ⧸ Ideal.span {V π}) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isDomain_quotient_span_V.solution
