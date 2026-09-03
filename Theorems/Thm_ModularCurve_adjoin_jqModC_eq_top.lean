import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Util
import P2M.Sol.S_ModularCurve_adjoin_jqModC_eq_top

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.adjoin_jqModC_eq_top (k₀ : Type*) [Field k₀] :
    IntermediateField.adjoin k₀
      ({⟨jqModC k₀, jqModC_mem_full k₀ 1⟩} : Set ↥(modularFunctionFieldFullC k₀ 1)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_adjoin_jqModC_eq_top.solution
