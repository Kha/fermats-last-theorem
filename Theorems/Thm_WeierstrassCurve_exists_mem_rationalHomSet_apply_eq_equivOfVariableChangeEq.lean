import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq

set_option autoImplicit false

theorem WeierstrassCurve.exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq
    {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) (γ : WeierstrassCurve.VariableChange k)
    {V : WeierstrassCurve k} (h : γ • W = V) :
    ∃ ι ∈ WeierstrassCurve.rationalHomSet k V W, ∃ ι' ∈ WeierstrassCurve.rationalHomSet k W V,
      (∀ P : V.toAffine.Point, ι P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq h P) ∧
        ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_apply_eq_equivOfVariableChangeEq.solution
