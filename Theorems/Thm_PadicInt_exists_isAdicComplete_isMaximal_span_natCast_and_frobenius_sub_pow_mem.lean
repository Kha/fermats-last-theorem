import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem

set_option autoImplicit false

theorem PadicInt.exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem
    (q : ℕ) [Fact q.Prime] :
    ∃ (Onr : Type) (_ : CommRing Onr) (_ : IsDomain Onr) (_ : IsDiscreteValuationRing Onr) (_ : CharZero Onr)
      (_ : Algebra ℤ_[q] Onr) (Fr : Onr ≃ₐ[ℤ_[q]] Onr),
      IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr ∧
      (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal ∧
      (∀ x : Onr, ∃ p : Polynomial ℤ_[q], p.Monic ∧
        Polynomial.aeval x p ∈ Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) ∧
      (∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
        ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) ∧
      (∀ x : Onr, Fr x - x ^ q ∈ Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem.solution
