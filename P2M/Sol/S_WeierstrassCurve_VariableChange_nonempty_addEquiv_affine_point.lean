import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import P2M.Util
namespace P2MW.S_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point

set_option maxHeartbeats 3200000
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {L : Type*} [Field L] [DecidableEq L] (W : WeierstrassCurve L)
    (C : WeierstrassCurve.VariableChange L) :
    Nonempty ((C • W).toAffine.Point ≃+ W.toAffine.Point) := by

  refine ⟨(AddEquiv.mk' (variableChangeEquiv C W).symm ?_).symm⟩
  intro P Q
  exact WeierstrassCurve.Affine.Point.vcInvFun_add C W P Q
