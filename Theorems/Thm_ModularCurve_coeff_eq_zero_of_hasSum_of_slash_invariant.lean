module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import P2M.Util
public import P2M.Sol.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant

@[expose] public section

theorem ModularCurve.coeff_eq_zero_of_hasSum_of_slash_invariant {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ} (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) {m : ℕ} (hm : m ≠ 0) : c m = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.solution
