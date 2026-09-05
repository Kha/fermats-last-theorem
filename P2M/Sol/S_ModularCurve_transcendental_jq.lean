module

public import Definitions.Def_ModularCurve_X0
public import Theorems.Thm_ModularCurve_aeval_jq_eq_zero
public import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_transcendental_jq

open ModularCurve IntermediateField

noncomputable section

theorem solution : Transcendental ℚ jq :=
  transcendental_iff.mpr fun _ hp => ModularCurve.aeval_jq_eq_zero hp

end
