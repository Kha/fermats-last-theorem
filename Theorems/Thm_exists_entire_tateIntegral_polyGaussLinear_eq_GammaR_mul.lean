import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Real.Sign
import P2M.Util
import P2M.Sol.S_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul

set_option autoImplicit false

theorem exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul (n δ : ℕ) (hδ : δ ≤ 1) :
    ∃ E : (Fin (n + 1) → ℂ) → ℝ → ℝ → ℂ → ℂ,
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), Differentiable ℂ (E c A B)) ∧
      (∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, 0 < z.re →
        ∫ ρ : ℝ, (∑ j : Fin (n + 1), c j * (ρ : ℂ) ^ (j : ℕ)) *
            (Real.exp (-(Real.pi * (A * ρ ^ 2 + 2 * B * ρ))) : ℂ) * (Real.sign ρ : ℂ) ^ δ * ((|ρ| : ℝ) : ℂ) ^ (z - 1) =
          Complex.Gammaℝ (z + δ) * E c A B z) ∧
      (∀ σ₁ σ₂ : ℝ, ∃ (C M : ℝ) (N : ℕ), ∀ (c : Fin (n + 1) → ℂ) (A B : ℝ), 0 < A → ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ →
        ‖E c A B z‖ ≤ C * (∑ j : Fin (n + 1), ‖c j‖) * max A A⁻¹ ^ N * (1 + |B|) ^ N *
          Real.exp (Real.pi * B ^ 2 / A) * Real.exp (M * |z.im|)) ∧
      (∀ z : ℂ, ContinuousOn (fun p : (Fin (n + 1) → ℂ) × ℝ × ℝ => E p.1 p.2.1 p.2.2 z)
        {p : (Fin (n + 1) → ℂ) × ℝ × ℝ | 0 < p.2.1}) := by p2m_exact_reverting @_root_.P2MW.S_exists_entire_tateIntegral_polyGaussLinear_eq_GammaR_mul.solution
