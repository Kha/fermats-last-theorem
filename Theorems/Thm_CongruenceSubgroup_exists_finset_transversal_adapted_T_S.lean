import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S

set_option autoImplicit false

open scoped MatrixGroups in

theorem CongruenceSubgroup.exists_finset_transversal_adapted_T_S
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hS₀ : ∀ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.S * ModularGroup.T ^ j) ∉ Γ)
    (h₀ : ℕ) (hh₀ : 0 < h₀) (hT : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ)
    (hmin : ∀ j : ℕ, 0 < j → j < h₀ → ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ) :
    ∃ s : Finset SL(2, ℤ),
      (∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ) ∧
      (∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) ∧
      (∀ j : ℕ, j < h₀ → ModularGroup.T ^ j ∈ s) ∧ ModularGroup.S ∈ s ∧
      (∀ x ∈ s, (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) → x ≠ ModularGroup.S →
        (∀ j : ℤ, x * ModularGroup.T ^ j ∉ Γ ∧ -(x * ModularGroup.T ^ j) ∉ Γ) ∧
        (x * ModularGroup.S⁻¹ ∉ Γ ∧ -(x * ModularGroup.S⁻¹) ∉ Γ)) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_exists_finset_transversal_adapted_T_S.solution
