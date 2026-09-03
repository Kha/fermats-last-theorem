import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet

theorem WeierstrassCurve.exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k] [DecidableEq k] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic] (u : (W.baseChange k).toAffine.Point →+ (W'.baseChange k).toAffine.Point) (hu : u ∈ WeierstrassCurve.rationalHomSet k W W') (u' : (W'.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) (hu' : u' ∈ WeierstrassCurve.rationalHomSet k W' W) (h : u'.comp u = AddMonoidHom.id ((W.baseChange k).toAffine.Point)) (h' : u.comp u' = AddMonoidHom.id ((W'.baseChange k).toAffine.Point)) : ∃ γ : WeierstrassCurve.VariableChange F, γ • W = W' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_of_comp_eq_id_of_mem_rationalHomSet.solution
