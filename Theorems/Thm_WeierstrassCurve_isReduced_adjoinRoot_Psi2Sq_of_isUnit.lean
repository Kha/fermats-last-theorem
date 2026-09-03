import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isReduced_adjoinRoot_Psi2Sq_of_isUnit

set_option autoImplicit false

universe u

theorem WeierstrassCurve.isReduced_adjoinRoot_Psi2Sq_of_isUnit
    {R : Type u} [CommRing R] [IsReduced R] (W : WeierstrassCurve R)
    (h2 : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) :
    IsReduced (AdjoinRoot W.Ψ₂Sq) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isReduced_adjoinRoot_Psi2Sq_of_isUnit.solution
