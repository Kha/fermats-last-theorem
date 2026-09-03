import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete

theorem WeierstrassCurve.exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete
    {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S) (hρ : Function.Surjective ρ)
    [IsAdicComplete (RingHom.ker ρ) R] (W : WeierstrassCurve R) (hW : IsUnit (3 * W.Δ))
    {x₀ y₀ : S} (heq : (W.map ρ).toAffine.Equation x₀ y₀) (hx₀ : (W.map ρ).Ψ₃.eval x₀ = 0)
    (hy₀ : IsUnit ((W.map ρ).toAffine.polynomialY.evalEval x₀ y₀)) :
    ∃ x y : R, W.toAffine.Equation x y ∧ W.Ψ₃.eval x = 0 ∧ ρ x = x₀ ∧ ρ y = y₀ ∧
      IsUnit (W.toAffine.polynomialY.evalEval x y) ∧
      ∀ x' y' : R, W.toAffine.Equation x' y' → W.Ψ₃.eval x' = 0 → ρ x' = x₀ → ρ y' = y₀ →
        x' = x ∧ y' = y := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_equation_and_eval_Psi3_eq_zero_and_map_eq_of_isAdicComplete.solution
