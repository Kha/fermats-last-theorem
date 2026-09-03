import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import P2M.Util
import P2M.Sol.S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd

set_option autoImplicit false

theorem exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ W : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, W (fun x => a * f x + b * g x) = fun x => a * W f x + b * W g x) ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ContDiff ℝ (⊤ : ℕ∞) (W f) ∧ HasCompactSupport (W f) ∧
        ((∀ x : ℝ, f (-x) = f x) → ∀ x : ℝ, W f (x ^ 2) = f x) ∧
        ((∀ x : ℝ, f (-x) = -f x) → ∀ x : ℝ, (x : ℂ) * W f (x ^ 2) = f x)) ∧
      ∀ H : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) ∧
          HasCompactSupport (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) := by p2m_exact_reverting @_root_.P2MW.S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd.solution
