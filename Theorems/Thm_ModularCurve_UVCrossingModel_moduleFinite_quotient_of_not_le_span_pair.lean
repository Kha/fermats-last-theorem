import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_ModularCurve_UVCrossingModel_moduleFinite_quotient_of_not_le_span_pair

set_option autoImplicit false

universe u
open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in

theorem ModularCurve.UVCrossingModel.moduleFinite_quotient_of_not_le_span_pair
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (J : Ideal (UVCrossingModel W (π ^ E)))
    (hJU : ¬ J ≤ Ideal.span {const (π ^ E) π, U (π ^ E)}) (hJV : ¬ J ≤ Ideal.span {const (π ^ E) π, V (π ^ E)}) :
    Module.Finite W (UVCrossingModel W (π ^ E) ⧸ J) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_UVCrossingModel_moduleFinite_quotient_of_not_le_span_pair.solution
