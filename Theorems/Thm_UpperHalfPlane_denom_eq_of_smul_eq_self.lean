import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_denom_eq_of_smul_eq_self

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem UpperHalfPlane.denom_eq_of_smul_eq_self
    (g : GL (Fin 2) ℝ) (hg : Matrix.GeneralLinearGroup.det g = 1) (τ₀ : ℍ) (hfix : g • τ₀ = τ₀) :
    ‖denom g τ₀‖ = 1 ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ = ((τ : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) * denom g τ₀) ∧
    (∀ τ : ℍ, (((g • τ : ℍ) : ℂ) - (τ₀ : ℂ)) * denom g τ * denom g τ₀ = (τ : ℂ) - (τ₀ : ℂ)) ∧
    (denom g τ₀ = 1 → g = 1) ∧
    (∀ h : GL (Fin 2) ℝ, Matrix.GeneralLinearGroup.det h = 1 → h • τ₀ = τ₀ → denom (g * h) τ₀ = denom g τ₀ * denom h τ₀) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_denom_eq_of_smul_eq_self.solution
