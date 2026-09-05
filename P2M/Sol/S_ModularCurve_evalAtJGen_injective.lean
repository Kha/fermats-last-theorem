module

import P2M.Sol.S_ModularCurve_PhiGen_evalAtJ_injective
import P2M.Util
public import Mathlib
public import Definitions.Def_ModularCurve_X0

namespace P2MW.S_ModularCurve_evalAtJGen_injective

open ModularCurve IntermediateField

theorem solution :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := by
  intro a b hab
  apply ModularCurve.PhiGen.evalAtJ_injective
  rw [← ModularCurve.algebraMap_comp_evalAtJGen, RingHom.comp_apply, RingHom.comp_apply, hab]
end S_ModularCurve_evalAtJGen_injective
end P2MW

public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve IntermediateField
theorem ModularCurve.evalAtJGen_injective :
    Function.Injective (ModularCurve.evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮ModularCurve.jq⟯) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_evalAtJGen_injective.solution
end
