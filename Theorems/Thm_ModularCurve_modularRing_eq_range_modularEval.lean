import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import P2M.Util
import P2M.Sol.S_ModularCurve_modularRing_eq_range_modularEval

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized
theorem ModularCurve.modularRing_eq_range_modularEval (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) :
    CharPReduction.modularRing N A = (NodeLocalized.modularEval N A).range := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularRing_eq_range_modularEval.solution
