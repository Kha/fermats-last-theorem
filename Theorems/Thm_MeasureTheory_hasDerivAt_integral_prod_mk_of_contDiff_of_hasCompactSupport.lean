import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => deriv (fun t : ℝ => Φ (t, p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × (Fin n → ℝ) => deriv (fun t : ℝ => Φ (t, p.2)) p.1) ∧
    ∀ x : ℝ, HasDerivAt (fun x : ℝ => ∫ y : Fin n → ℝ, Φ (x, y))
      (∫ y : Fin n → ℝ, deriv (fun t : ℝ => Φ (t, y)) x) x := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport.solution
