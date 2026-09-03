import Mathlib
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (χ : Γ → ℂ)
    (hmul : ∀ γ δ, χ (γ * δ) = χ γ * χ δ) (hunit : ∀ γ, ‖χ γ‖ = 1)
    (htriv : ∀ γ : Γ,
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → χ γ = 1) :
    ∃ φ : Additive Γ →+ ℝ,
      (∀ γ : Γ,
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ (Additive.ofMul γ) = 0) ∧
      ∀ γ, χ γ = Complex.exp (2 * Real.pi * Complex.I * (φ (Additive.ofMul γ) : ℂ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_addMonoidHom_exp_eq_of_norm_eq_one_of_trace_sq_le_four_of_finiteIndex.solution
