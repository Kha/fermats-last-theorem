import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (S : Finset ℍ) (n : ℍ → ℕ) :
    ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ P : ModularForm Γ k, (P : ℍ → ℂ) ≠ 0 ∧
      ∀ τ ∈ S, ((n τ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z)) (τ : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology.solution
