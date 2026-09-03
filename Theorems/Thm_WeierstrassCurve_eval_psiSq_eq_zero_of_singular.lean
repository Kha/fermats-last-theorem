import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_eval_psiSq_eq_zero_of_singular

open WeierstrassCurve Polynomial
theorem WeierstrassCurve.eval_psiSq_eq_zero_of_singular {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x₀ y₀ : R} (he : W.toAffine.Equation x₀ y₀) (hFx : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) (hFy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0) {n : ℤ} (hn : 1 < n.natAbs) : (W.ΨSq n).eval x₀ = 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_eval_psiSq_eq_zero_of_singular.solution
