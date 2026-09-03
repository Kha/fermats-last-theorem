import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.rsLocal_fe32_of_mul_eq_middle_of_eq_rational
    (N : ℕ) (hN : 1 < N) (Z D : ℂ → ℂ) (E Ed : Polynomial ℂ) (ε a₁ a₂ : ℂ)
    (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ) (hq : q ≠ 0) (hqd : qd ≠ 0)
    (hZ : ∀ s : ℂ, σ₂ < s.re → Z s * q.eval ((N : ℂ) ^ (-s)) = p.eval ((N : ℂ) ^ (-s)))
    (hD : ∀ s : ℂ, σ₃ < (1 - s).re →
      D s * qd.eval ((N : ℂ) ^ (-(1 - s))) = pd.eval ((N : ℂ) ^ (-(1 - s))))

    (m₁ m₂ : Polynomial ℂ) (k : ℤ) (hm₂ : m₂ ≠ 0)
    (σP σD : ℝ)
    (hP : ∀ s : ℂ, σP < s.re →
      Z s * E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          m₂.eval ((N : ℂ) ^ (-s)) =
        m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))
    (hDM : ∀ s : ℂ, σD < (1 - s).re →
      D s * Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) * Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          m₂.eval ((N : ℂ) ^ (-s)) =
        ε ^ 2 * (m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))) :
    ∀ s : ℂ,
      pd.eval ((N : ℂ) ^ (-(1 - s))) * q.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p.eval ((N : ℂ) ^ (-s)) * qd.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational.solution
