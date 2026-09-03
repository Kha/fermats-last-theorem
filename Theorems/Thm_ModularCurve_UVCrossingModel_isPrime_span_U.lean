import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_isPrime_span_U

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.isPrime_span_U {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] : (Ideal.span {U π}).IsPrime := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_isPrime_span_U.solution
