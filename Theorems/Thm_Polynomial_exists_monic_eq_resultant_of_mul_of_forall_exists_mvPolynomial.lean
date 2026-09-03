import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial

set_option autoImplicit false

theorem Polynomial.exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
    (K : Type*) [Field K] (D : Polynomial ℤ → ℚ) (n : ℕ) (hn : Even n) (h1 : D 1 = 1)
    (hmul : ∀ G H : Polynomial ℤ, G.Monic → H.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
      ((H.coeff 0 : ℤ) : K) ≠ 0 → D (G * H) = D G * D H)
    (hpoly : ∀ b : ℕ, ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ n ∧
      N.coeff (Finsupp.single 0 n) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N = D G) :
    ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = n ∧
      ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        D G = (G.map (Int.castRingHom ℚ)).resultant P := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial.solution
