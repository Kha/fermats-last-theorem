import Mathlib
import Definitions.Def_IncidenceSystem
import P2M.Util
import P2M.Sol.S_IncidenceSystem_Data_isUnit_det_jacobian_iff

set_option autoImplicit false

open MvPolynomial IncidenceSystem

theorem IncidenceSystem.Data.isUnit_det_jacobian_iff
    {g e m' : ℕ} {A : Type*} [CommRing A] (D : IncidenceSystem.Data g e m' A) (pt : Var g e m' → A)
    (htri : ∀ i (j j' : Fin e), j < j' → MvPolynomial.pderiv (some j') (D.G i j) = 0)
    (hc : ∀ k, pt (Var.c k) = 0)
    (hσ : ∀ i r, pt (Var.σ none i r) = if (r : ℕ) = 0 then 1 else 0)
    (hp : ∀ i, D.p none i = (MvPolynomial.X none - MvPolynomial.C (pt (Var.u i))) ^ (m' + 1))
    (hs : ∀ i, D.s none i = 1)
    (hG : ∀ i j, IsUnit (D.dG pt i j)) (hsv : ∀ k i, IsUnit (D.sVal pt k i)) :
    IsUnit (D.jacobian pt).det ↔ IsUnit (((m' + 1 : ℕ) : A) ^ g) ∧ IsUnit (D.tcMatrix pt).det := by p2m_exact_reverting @_root_.P2MW.S_IncidenceSystem_Data_isUnit_det_jacobian_iff.solution
