import Mathlib
import P2M.Util
import P2M.Sol.S_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul

set_option autoImplicit false

universe u

theorem MvFormalGroup.smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (n : ℕ) :
    (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (n + 1)
      = ∑ m ∈ Finset.range (n + 1),
          a (n - m) * (Matrix.of fun i j => (MvPolynomial.X (m, i, j) :
            MvPolynomial (ℕ × Fin d × Fin d) (Padic p))).map
              (⇑(MvPolynomial.aeval fun v =>
                (MvPolynomial.X v : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ p))^[n - m] := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul.solution
