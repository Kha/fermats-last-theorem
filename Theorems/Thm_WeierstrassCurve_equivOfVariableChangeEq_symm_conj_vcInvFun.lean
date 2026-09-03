import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_equivOfVariableChangeEq_symm_conj_vcInvFun

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem WeierstrassCurve.equivOfVariableChangeEq_symm_conj_vcInvFun
    {K : Type*} [Field K] [DecidableEq K]
    (E : WeierstrassCurve K) (C γ : WeierstrassCurve.VariableChange K) (hγ : γ • E = E) :
    ∃ hγ' : (C * γ * C⁻¹) • (C • E) = C • E,
      ∀ T : E.toAffine.Point,
        (Point.equivOfVariableChangeEq (W := (C • E).toAffine) hγ').symm (Point.vcInvFun C E.toAffine T) =
          Point.vcInvFun C E.toAffine ((Point.equivOfVariableChangeEq (W := E.toAffine) hγ).symm T) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_equivOfVariableChangeEq_symm_conj_vcInvFun.solution
