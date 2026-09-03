import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (k : ℤ) (hk : 4 ≤ k)
    (φ : ℍ → ℂ) (hφ : MDiff φ)
    (hdecay : ∃ M : ℝ, ∀ w : ℍ, ‖φ w‖ * ‖(w : ℂ) + Complex.I‖ ^ k ≤ M) :

    (∀ τ₀ : ℍ, ∃ U : Set ℍ, IsOpen U ∧ τ₀ ∈ U ∧ ∃ u : ↥Γ → ℝ, Summable u ∧
        ∀ (γ : ↥Γ) (τ : ℍ), τ ∈ U → ‖φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)‖ ≤ u γ) ∧

    ∃ P : ModularForm Γ k, ∀ τ : ℍ, P τ = ∑' γ : ↥Γ, φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology.solution
