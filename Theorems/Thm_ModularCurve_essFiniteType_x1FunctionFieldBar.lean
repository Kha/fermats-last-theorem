import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_essFiniteType_x1FunctionFieldBar

set_option autoImplicit false

p2m_open "AlgebraicCurve~essFiniteType_of_transcendental_of_finiteDimensional ModularCurve"

theorem ModularCurve.essFiniteType_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_essFiniteType_x1FunctionFieldBar.solution
