import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_modularForm_mul_eq_of_analyticOrderAt_le (N : ℕ) {a b : ℤ} (c : ℤ) (habc : b + c = a)
    (Φ : ModularForm (CongruenceSubgroup.Gamma0 N) a) (Ψ : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hΨ : Ψ ≠ 0)
    (hord : ∀ τ : UpperHalfPlane, analyticOrderAt ((Ψ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((Φ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ))
    (hcusp : ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ C : ℝ,
      ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖((Φ : UpperHalfPlane → ℂ) ∣[a] (A : GL (Fin 2) ℝ)) τ‖ ≤ C * ‖((Ψ : UpperHalfPlane → ℂ) ∣[b] (A : GL (Fin 2) ℝ)) τ‖) :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) c, ∀ τ : UpperHalfPlane, f τ * Ψ τ = Φ τ := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_modularForm_mul_eq_of_analyticOrderAt_le.solution
