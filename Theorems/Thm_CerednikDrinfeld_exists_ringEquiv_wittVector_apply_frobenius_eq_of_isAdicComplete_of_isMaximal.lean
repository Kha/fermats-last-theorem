import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal

set_option autoImplicit false

theorem CerednikDrinfeld.exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
    (r : ℕ) [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr]
    (ϖ : Onr) (hϖ : Ideal.span {ϖ} = Ideal.span {((r : ℕ) : Onr)})
    (hcomplete : IsAdicComplete (Ideal.span {ϖ}) Onr)
    (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hclosed : ∀ q : Polynomial Onr, q.Monic → 0 < q.natDegree → ∃ x : Onr, Polynomial.eval x q ∈ Ideal.span {ϖ})
    (Fr : Onr ≃+* Onr) (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {ϖ}) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k r) (_ : IsAlgClosed k) (e : WittVector r k ≃+* Onr)
      (q : Onr →+* k),
      (∀ x : WittVector r k, e (WittVector.frobenius x) = Fr (e x)) ∧
      Function.Surjective q ∧ RingHom.ker q = Ideal.span {ϖ} ∧
      (∀ x : WittVector r k, q (e x) = x.coeff 0) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal.solution
