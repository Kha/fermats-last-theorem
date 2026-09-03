import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_CuspSpace_card_fromCoset_fiber

open OnePoint
open scoped MatrixGroups
theorem ModularCurve.CuspSpace.card_fromCoset_fiber {N : ℕ} [NeZero N] (x : ModularCurve.CuspSpace N) :
    Nat.card {y : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N // ModularCurve.CuspSpace.fromCoset N y = x} = ModularCurve.CuspSpace.cuspWidth x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_card_fromCoset_fiber.solution
