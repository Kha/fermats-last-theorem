import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (hpat : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, (P i).ord (t i) = 1)
    (u : Fin M → F) (hu : ∀ i j, u j ∈ (P i).toValuationSubring)
    (c : Place K F → F) (hc : ∀ i, c (P i) ∈ (P i).toValuationSubring) :
    (Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (u j * c (P i))).det
      = (∏ i, (P i).evalAt (c (P i))) * (jetMatrix P t e u).det := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix.solution
