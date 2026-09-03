import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) :

    (∀ τ σ : ℍ, (∀ γ ∈ Γ, γ • τ ≠ σ) →
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ) ∧

    (∀ τ : ℍ, ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_separate_and_localParameter_of_discreteTopology.solution
