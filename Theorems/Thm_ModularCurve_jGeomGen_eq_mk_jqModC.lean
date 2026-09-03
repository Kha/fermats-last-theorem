import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
import P2M.Sol.S_ModularCurve_jGeomGen_eq_mk_jqModC
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.jGeomGen_eq_mk_jqModC (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    jGeomGen K N = ⟨jqModC K, jqModC_mem K N⟩ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jGeomGen_eq_mk_jqModC.solution
