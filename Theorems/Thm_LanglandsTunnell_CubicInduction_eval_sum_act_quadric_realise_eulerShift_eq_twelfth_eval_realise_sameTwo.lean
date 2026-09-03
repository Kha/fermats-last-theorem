import Mathlib
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_eulerShift_eq_twelfth_eval_realise_sameTwo

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_eulerShift_eq_twelfth_eval_realise_sameTwo
    (ν : Fin 3 → ℂ) (j : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (hp : p.IsHomogeneous 2)
    (k : Fin 3 × Fin 3 → ℂ)
    (hk : ∀ i j : Fin 3, (∑ a : Fin 3, k (i, a) * k (j, a)) = if i = j then 1 else 0) :
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
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let realise : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun q => MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q
    MvPolynomial.eval k
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
          MvPolynomial.C (1 / 2 : ℂ) *
            (act ν a b (MvPolynomial.C (1 / 2 : ℂ) *
                (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
                realise (MvPolynomial.X i' * MvPolynomial.pderiv i p -
                  MvPolynomial.C (1 / 3 : ℂ) * (∑ e : Fin 3, MvPolynomial.X e ^ 2) *
                    MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) +
             act ν b a (MvPolynomial.C (1 / 2 : ℂ) *
                (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
                realise (MvPolynomial.X i' * MvPolynomial.pderiv i p -
                  MvPolynomial.C (1 / 3 : ℂ) * (∑ e : Fin 3, MvPolynomial.X e ^ 2) *
                    MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))))) =
      MvPolynomial.eval k (MvPolynomial.C (1 / 12 : ℂ) * realise (same₂ (Ξ ν p))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_eulerShift_eq_twelfth_eval_realise_sameTwo.solution
