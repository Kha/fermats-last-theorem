import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational
    (N : ℕ) (hN : 1 < N) (Z D : ℂ → ℂ) (E Ed : Polynomial ℂ) (ε a₁ a₂ : ℂ)

    (p₀ q₀ pd₀ qd₀ : Polynomial ℂ) (σ₀ σd₀ : ℝ) (hq₀ : q₀ ≠ 0) (hqd₀ : qd₀ ≠ 0)
    (hZ₀ : ∀ s : ℂ, σ₀ < s.re → Z s * q₀.eval ((N : ℂ) ^ (-s)) = p₀.eval ((N : ℂ) ^ (-s)))
    (hD₀ : ∀ s : ℂ, σd₀ < (1 - s).re →
      D s * qd₀.eval ((N : ℂ) ^ (-(1 - s))) = pd₀.eval ((N : ℂ) ^ (-(1 - s))))
    (hFE₀ : ∀ s : ℂ,
      pd₀.eval ((N : ℂ) ^ (-(1 - s))) * q₀.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p₀.eval ((N : ℂ) ^ (-s)) * qd₀.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2)

    (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ) (hq : q ≠ 0) (hqd : qd ≠ 0)
    (hZ : ∀ s : ℂ, σ₂ < s.re → Z s * q.eval ((N : ℂ) ^ (-s)) = p.eval ((N : ℂ) ^ (-s)))
    (hD : ∀ s : ℂ, σ₃ < (1 - s).re →
      D s * qd.eval ((N : ℂ) ^ (-(1 - s))) = pd.eval ((N : ℂ) ^ (-(1 - s)))) :
    ∀ s : ℂ,
      pd.eval ((N : ℂ) ^ (-(1 - s))) * q.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p.eval ((N : ℂ) ^ (-s)) * qd.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational.solution
