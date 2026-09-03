import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six

set_option autoImplicit false

theorem WeierstrassCurve.VariableChange.eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six
    (R : Type) [CommRing R] (h6 : IsUnit (6 : R))
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (hC : C • W = W) (hu : C.u = 1) :
    C = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six.solution
