import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {a b : ℤ} (c : ℤ) (habc : b + c = a)
    (Φ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) (Ψ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) (hΨ : Ψ ≠ 0)
    (hord : ∀ τ : UpperHalfPlane, analyticOrderAt ((Ψ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((Φ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ))
    (hcusp : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ), 0 < ε →
      ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖((Φ : UpperHalfPlane → ℂ) ∣[a] (A : GL (Fin 2) ℝ)) τ‖ ≤ ε * ‖((Ψ : UpperHalfPlane → ℂ) ∣[b] (A : GL (Fin 2) ℝ)) τ‖) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) c, ∀ τ : UpperHalfPlane, f τ * Ψ τ = Φ τ := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le.solution
