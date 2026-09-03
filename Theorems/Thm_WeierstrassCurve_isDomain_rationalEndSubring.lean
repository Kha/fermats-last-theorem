import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isDomain_rationalEndSubring

set_option autoImplicit false

open scoped Quaternion TensorProduct

theorem WeierstrassCurve.isDomain_rationalEndSubring
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
    (X : WeierstrassCurve k) [X.IsElliptic] :
    IsDomain ↥(WeierstrassCurve.rationalEndSubring k X) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isDomain_rationalEndSubring.solution
