import Mathlib
import Theorems.Thm_Complex_forall_cpow_mul_eval_mul_eval_eq_and_exists_finset_forall_eq_mul_of_infinite
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.forall_cleared_fe_of_laurent_fe_of_rational_forms
    (q : ℕ) (hq : 1 < q) (Z Zd γ : ℂ → ℂ)

    (P₀ Pd₀ : Polynomial ℂ) (m₀ md₀ : ℤ) (σ₀ σd₀ : ℝ)
    (hZ₀ : ∀ s : ℂ, σ₀ < s.re → Z s = (q : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((q : ℂ) ^ (-s)))
    (hZd₀ : ∀ s : ℂ, σd₀ < s.re → Zd s = (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)))
    (hFE₀ : ∀ s : ℂ, (q : ℂ) ^ ((md₀ : ℂ) * s) * Pd₀.eval ((q : ℂ) ^ (-s)) =
      γ s * ((q : ℂ) ^ ((m₀ : ℂ) * (-s)) * P₀.eval ((q : ℂ) ^ s)))

    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (σ σd : ℝ) (hQ : Q ≠ 0) (hQd : Qd ≠ 0)
    (hZ : ∀ s : ℂ, σ < s.re → Z s * Q.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((m : ℂ) * s) * P.eval ((q : ℂ) ^ (-s)))
    (hZd : ∀ s : ℂ, σd < s.re →
      Zd s * Qd.eval ((q : ℂ) ^ (-s)) = (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s))) :
    ∀ s : ℂ, (q : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((q : ℂ) ^ (-s)) * Q.eval ((q : ℂ) ^ s) =
      γ s * ((q : ℂ) ^ ((m : ℂ) * (-s)) * P.eval ((q : ℂ) ^ s)) * Qd.eval ((q : ℂ) ^ (-s)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_forall_cleared_fe_of_laurent_fe_of_rational_forms.solution
