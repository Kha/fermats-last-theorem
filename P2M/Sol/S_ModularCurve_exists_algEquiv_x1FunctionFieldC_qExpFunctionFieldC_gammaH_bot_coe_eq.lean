import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import P2M.Util
namespace P2MW.S_ModularCurve_exists_algEquiv_x1FunctionFieldC_qExpFunctionFieldC_gammaH_bot_coe_eq

set_option autoImplicit false

open ModularCurve

namespace IntermediateField p2m_export "IntermediateField" "equivOfEq" end IntermediateField
p2m_open_scoped "IntermediateField" in

theorem IntermediateField.coe_equivOfEq_apply' {F E : Type*} [Field F] [Field E] [Algebra F E]
    {S T : IntermediateField F E} (h : S = T) (x : ↥S) : ((IntermediateField.equivOfEq h x : ↥T) : E) = (x : E) := by
  simp only [IntermediateField.equivOfEq]
  rfl

theorem solution
    (k : Type*) [Field k] (M : ℕ) [NeZero M] :
    ∃ e : ↥(x1FunctionFieldC k M) ≃ₐ[k] ↥(qExpFunctionFieldC k (CohCarrier.GammaH M ⊥)),
      ∀ x : ↥(x1FunctionFieldC k M),
        ((e x : ↥(qExpFunctionFieldC k (CohCarrier.GammaH M ⊥))) : LaurentSeries k) = (x : LaurentSeries k) := by

  have h : x1FunctionFieldC k M = qExpFunctionFieldC k (CohCarrier.GammaH M ⊥) := by
    unfold x1FunctionFieldC
    rw [ModularCurve.GammaH_bot]
  exact ⟨IntermediateField.equivOfEq h, fun x => IntermediateField.coe_equivOfEq_apply' h x⟩
