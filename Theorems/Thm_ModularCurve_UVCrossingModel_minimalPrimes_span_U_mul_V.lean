import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_minimalPrimes_span_U_mul_V

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.minimalPrimes_span_U_mul_V {W : Type*} [CommRing W] (π : W) [IsDomain (W ⧸ Ideal.span {π})] : (Ideal.span {U π * V π}).minimalPrimes = {Ideal.span {U π}, Ideal.span {V π}} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_minimalPrimes_span_U_mul_V.solution
