import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (τ₀ σ₀ : ℍ) :
    ∃ U : Set ℍ, IsOpen U ∧ σ₀ ∈ U ∧ ∃ A ϑ : ℝ, 0 ≤ A ∧ 0 ≤ ϑ ∧ ϑ < 1 ∧
      ∀ (n : ℕ) (k : ℤ), 4 ≤ k →
        ∃ P : ModularForm Γ k,
          (∀ τ : ℍ, P τ = ∑' γ : ↥Γ,
            (((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)) ∧
          (∀ σ : ℍ, σ ∈ U →
            ‖P σ - ∑' γ : ↥Γ, Set.indicator {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • σ₀ = τ₀} (fun γ : ↥Γ =>
              (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)) γ‖
              ≤ A * ϑ ^ k * (2 * Real.sqrt (σ.im * τ₀.im)) ^ (-k)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology.solution
