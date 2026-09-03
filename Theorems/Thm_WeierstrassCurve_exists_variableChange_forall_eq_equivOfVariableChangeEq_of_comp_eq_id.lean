import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id

theorem WeierstrassCurve.exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (W W' : WeierstrassCurve k) [W.IsElliptic] [W'.IsElliptic]
    (u : W.toAffine.Point →+ W'.toAffine.Point) (hu : u ∈ WeierstrassCurve.rationalHomSet k W W')
    (u' : W'.toAffine.Point →+ W.toAffine.Point) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W)
    (h : u'.comp u = AddMonoidHom.id _) (h' : u.comp u' = AddMonoidHom.id _) :
    ∃ (γ : WeierstrassCurve.VariableChange k) (hγ : γ • W' = W),
      ∀ P, u P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ P := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id.solution
