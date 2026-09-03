import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_isPrincipal_sub_of_isRepOf
import Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.isPrincipal_sub_of_isRepOf (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] {n : ℕ}
    {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : JZero.IsRepOf N K n c D) (h' : JZero.IsRepOf N K n c D') :
    Divisor.IsPrincipal (D' - D) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_isPrincipal_sub_of_isRepOf.solution
