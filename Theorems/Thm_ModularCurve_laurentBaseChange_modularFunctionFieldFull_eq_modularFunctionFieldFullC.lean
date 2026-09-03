import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
    (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    laurentBaseChange K (modularFunctionFieldFull N) = modularFunctionFieldFullC K N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC.solution
