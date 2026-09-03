import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero

set_option autoImplicit false

theorem AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F')

    (z : F') (hgen : ∀ x : F', ∃ p : Polynomial F, Polynomial.eval₂ φ.toRingHom z p = x)

    (g : Polynomial F) (hg : g.Monic)
    (hgO : ∀ i : ℕ, 0 ≤ (w.restrictAlong φ hφ).ord (g.coeff i))
    (hgz : Polynomial.eval₂ φ.toRingHom z g = 0)

    (hne : Polynomial.eval₂ φ.toRingHom z (Polynomial.derivative g) ≠ 0)
    (hsimple : w.ord (Polynomial.eval₂ φ.toRingHom z (Polynomial.derivative g)) = 0) :
    AlgebraicCurve.Place.ramificationIndexAlong φ w = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero.solution
