import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self

set_option autoImplicit false

open WeierstrassCurve

theorem WeierstrassCurve.variableChange_mk_neg_one_smul_eq_self
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange R) • W = W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self.solution
