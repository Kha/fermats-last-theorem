import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in
theorem WeierstrassCurve.Affine.Point.exists_addEquiv_nodeNormalForm_additive_units
    {L : Type*} [Field L] [CharZero L] [DecidableEq L] (d : L) (hd : d ≠ 0) :
    ∃ e : (⟨0, d * d, 0, 0, 0⟩ : WeierstrassCurve L).toAffine.Point ≃+ Additive Lˣ,
      ∀ x y h, ((Additive.toMul (e (Point.some x y h)) : Lˣ) : L) * (y + d * x) = y - d * x := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units.solution
