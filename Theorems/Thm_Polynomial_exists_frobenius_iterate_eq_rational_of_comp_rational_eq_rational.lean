import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational

theorem Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
    {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [IsAlgClosed k]
    (fn fd gn gd : Polynomial F) (hf : ∀ c : F, fn ≠ Polynomial.C c * fd)
    (m : k → k) (S : Set k) (hS : S.Finite)
    (H : ∀ x : k, x ∉ S → Polynomial.aeval x fd ≠ 0 ∧ Polynomial.aeval x gd ≠ 0 ∧
      m (Polynomial.aeval x fn / Polynomial.aeval x fd) =
        Polynomial.aeval x gn / Polynomial.aeval x gd) :
    ∃ (t : ℕ) (hn hd : Polynomial F) (T : Set k), T.Finite ∧ ∀ u : k, u ∉ T →
      Polynomial.aeval u hd ≠ 0 ∧
        m u ^ ringExpChar F ^ t = Polynomial.aeval u hn / Polynomial.aeval u hd := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational.solution
