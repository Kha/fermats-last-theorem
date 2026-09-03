import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import P2M.Util
namespace P2MW.S_ModularCurve_jGeomGen_eq_mk_jqModC
set_option autoImplicit false

open ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    jGeomGen K N = ⟨jqModC K, jqModC_mem K N⟩ := rfl
