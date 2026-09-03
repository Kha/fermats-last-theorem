import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_finite_rationalHomSet_units

theorem WeierstrassCurve.finite_rationalHomSet_units {F : Type*} [Field F] (k : Type*) [Field k] [DecidableEq k] [Algebra F k] [IsAlgClosed k] (W : WeierstrassCurve F) [W.IsElliptic] : {u : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point | u ∈ WeierstrassCurve.rationalHomSet k W W ∧ ∃ v ∈ WeierstrassCurve.rationalHomSet k W W, u.comp v = AddMonoidHom.id _ ∧ v.comp u = AddMonoidHom.id _}.Finite := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_finite_rationalHomSet_units.solution
