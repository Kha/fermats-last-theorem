import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import P2M.Util
import P2M.Sol.S_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.diamondAutHBar_eq_refl_of_mem_or_neg_mem (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ) (hd : d ∈ H ∨ -d ∈ H) :
    ModularCurve.diamondAutHBar M H d = AlgEquiv.refl := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_diamondAutHBar_eq_refl_of_mem_or_neg_mem.solution
