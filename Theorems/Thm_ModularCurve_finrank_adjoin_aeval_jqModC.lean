import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import P2M.Sol.S_ModularCurve_transcendental_jqModC
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_aeval_jqModC

set_option autoImplicit false

open Polynomial ModularCurve
theorem ModularCurve.finrank_adjoin_aeval_jqModC (k₀ : Type*) [Field k₀] (r : k₀[X]) (hr : 0 < r.natDegree) :
    Module.finrank
        ↥(IntermediateField.adjoin k₀
          ({Polynomial.aeval (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) r} :
            Set ↥(modularFunctionFieldFullC k₀ 1)))
        ↥(modularFunctionFieldFullC k₀ 1) = r.natDegree := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_aeval_jqModC.solution
