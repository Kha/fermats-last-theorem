import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair

open ModularCurve ModularCurve.UVCrossingModel
theorem ModularCurve.UVCrossingModel.maximalIdeal_eq_span_pair {W : Type*} [CommRing W] [IsLocalRing W] {π : W} (hW : IsLocalRing.maximalIdeal W = Ideal.span {π}) [IsLocalRing (UVCrossingModel W π)] : IsLocalRing.maximalIdeal (UVCrossingModel W π) = Ideal.span {U π, V π} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_maximalIdeal_eq_span_pair.solution
