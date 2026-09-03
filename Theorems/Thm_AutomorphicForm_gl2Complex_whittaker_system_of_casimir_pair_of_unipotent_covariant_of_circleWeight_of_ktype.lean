import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import P2M.Util
import P2M.Sol.S_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
    (n : ℕ) (F : Fin (n + 1) → GL (Fin 2) ℂ → ℂ) (κ lam lam' : ℂ)
    (DF : Fin (n + 1) → ArchDirComplex → GL (Fin 2) ℂ → ℂ)
    (DD : Fin (n + 1) → ArchDirComplex → ArchDirComplex → GL (Fin 2) ℂ → ℂ)
    (hD : ∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => F p (h * archFlowMatrixComplex d t)) (DF p d h) 0)
    (hDD : ∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => DF p d (h * archFlowMatrixComplex d' t)) (DD p d' d h) 0)
    (hΩ : ∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .H .H h - Complex.I * DD p .H .iH h) -
            Complex.I * ((1 / 2 : ℂ) * (DD p .iH .H h - Complex.I * DD p .iH .iH h)))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DF p .H h - Complex.I * DF p .iH h)) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .E .Fm h - Complex.I * DD p .E .iFm h) -
            Complex.I * ((1 / 2 : ℂ) * (DD p .iE .Fm h - Complex.I * DD p .iE .iFm h)))) = lam * F p h)
    (hΩ' : ∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .H .H h + Complex.I * DD p .H .iH h) +
            Complex.I * ((1 / 2 : ℂ) * (DD p .iH .H h + Complex.I * DD p .iH .iH h)))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DF p .H h + Complex.I * DF p .iH h)) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (DD p .E .Fm h + Complex.I * DD p .E .iFm h) +
            Complex.I * ((1 / 2 : ℂ) * (DD p .iE .Fm h + Complex.I * DD p .iE .iFm h)))) = lam' * F p h)
    (hN : ∀ (p : Fin (n + 1)) (x : ℂ) (h : GL (Fin 2) ℂ),
      F p (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * ((2 * (κ * x).re : ℝ) : ℂ)) * F p h)
    (hM : ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      F p (h * circleGL2 ζ) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * F p h)
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), E₁ s p' p * F p' h)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        F p (h * k) = ∑ p' : Fin (n + 1), E₂ s p' p * F p' h) :
    let f : ℕ → ℝ → ℂ := fun m y =>
      if hm : m < n + 1 then F ⟨m, hm⟩ (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)) else 0
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.solution
