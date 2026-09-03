import Definitions.Def_ModularCurve_SL2Elementary
import Mathlib.Data.ZMod.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_closure_elemSet_eq_top

theorem ModularCurve.closure_elemSet_eq_top (N : ℕ) [NeZero N] :
    Subgroup.closure (ModularCurve.elemSet (ZMod N)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_closure_elemSet_eq_top.solution
