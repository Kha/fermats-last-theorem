import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic

theorem WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic.solution
