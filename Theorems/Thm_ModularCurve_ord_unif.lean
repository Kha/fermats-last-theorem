import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import P2M.Util
import P2M.Sol.S_ModularCurve_ord_unif

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_unif (K : Type) [Field K] (N : ℕ) [NeZero N]
    (x : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) : x.ord (ModularCurve.unif N K x) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ord_unif.solution
