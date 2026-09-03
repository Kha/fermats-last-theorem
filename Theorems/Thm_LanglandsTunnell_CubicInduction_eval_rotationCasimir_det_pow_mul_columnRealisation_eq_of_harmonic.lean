import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic
    (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) (j : Fin 3) (d : ℕ)
    (o : Fin 3 → Fin 3 → ℝ) (ho : (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)) :
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
    let Ω : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun P => (act ν 0 1 (act ν 0 1 P - act ν 1 0 P) - act ν 1 0 (act ν 0 1 P - act ν 1 0 P)) +
        (act ν 0 2 (act ν 0 2 P - act ν 2 0 P) - act ν 2 0 (act ν 0 2 P - act ν 2 0 P)) +
        (act ν 1 2 (act ν 1 2 P - act ν 2 1 P) - act ν 2 1 (act ν 1 2 P - act ν 2 1 P))
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
        (Ω ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ d *
          MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) =
      -(((ℓ : ℂ) * ((ℓ : ℂ) + 1))) *
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ))
          ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ d *
            MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic.solution
