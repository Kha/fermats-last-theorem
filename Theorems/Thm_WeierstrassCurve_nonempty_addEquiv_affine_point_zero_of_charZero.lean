import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_nonempty_addEquiv_affine_point_zero_of_charZero

theorem WeierstrassCurve.nonempty_addEquiv_affine_point_zero_of_charZero
    (L : Type*) [Field L] [CharZero L] [DecidableEq L] :
    Nonempty ((⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve L).toAffine.Point ≃+ L) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_nonempty_addEquiv_affine_point_zero_of_charZero.solution
