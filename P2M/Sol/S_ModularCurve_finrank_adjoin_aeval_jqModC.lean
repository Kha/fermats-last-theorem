import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_adjoin_jqModC_eq_top
import Theorems.Thm_IntermediateField_finrank_adjoin_aeval_of_transcendental
import P2M.Util
namespace P2MW.S_ModularCurve_finrank_adjoin_aeval_jqModC

set_option autoImplicit false

open Polynomial ModularCurve

theorem solution (k₀ : Type*) [Field k₀] (r : k₀[X]) (hr : 0 < r.natDegree) :
    Module.finrank
        ↥(IntermediateField.adjoin k₀
          ({Polynomial.aeval (⟨jqModC k₀, jqModC_mem_full k₀ 1⟩ : ↥(modularFunctionFieldFullC k₀ 1)) r} :
            Set ↥(modularFunctionFieldFullC k₀ 1)))
        ↥(modularFunctionFieldFullC k₀ 1) = r.natDegree :=
  IntermediateField.finrank_adjoin_aeval_of_transcendental _
    (fun h => ModularCurve.transcendental_jqModC k₀ (h.algHom (IntermediateField.val _)))
    (ModularCurve.adjoin_jqModC_eq_top k₀) r hr
