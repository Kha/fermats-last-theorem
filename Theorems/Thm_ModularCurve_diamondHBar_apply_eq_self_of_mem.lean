import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondHBar_apply_eq_self_of_mem
attribute [-simp] ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.diamondHBar_apply_eq_self_of_mem
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) (hd : d ∈ H) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H d x = x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondHBar_apply_eq_self_of_mem.solution
