import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_inducedPicture_act_diag_row_eq_and_harmonic_split

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.inducedPicture_act_diag_row_eq_and_harmonic_split
    (ν : Fin 3 → ℂ) (m a : Fin 3) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let γ : Fin 3 → ℂ := fun c => ν c + (![1, 0, -1] : Fin 3 → ℂ) c + (if c < m then (1 : ℂ) else if m < c then (-1 : ℂ) else 0)
    let lam : ℂ := (ν 0 + ν 1 + ν 2 + 2 * ν m) / 5
    let p₃ : MvPolynomial (Fin 3) ℂ :=
      MvPolynomial.X m * ∑ c : Fin 3, MvPolynomial.C (γ c - lam) * MvPolynomial.X c ^ 2
    act ν a a (MvPolynomial.X (m, a)) =
        MvPolynomial.X (m, a) * ∑ c : Fin 3, MvPolynomial.C (γ c) * MvPolynomial.X (c, a) ^ 2 ∧
      MvPolynomial.X (m, a) * ∑ c : Fin 3, MvPolynomial.C (γ c) * MvPolynomial.X (c, a) ^ 2 =
        MvPolynomial.C lam * MvPolynomial.X (m, a) * (∑ c : Fin 3, MvPolynomial.X (c, a) ^ 2) +
          MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, a) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p₃ ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p₃)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_inducedPicture_act_diag_row_eq_and_harmonic_split.solution
