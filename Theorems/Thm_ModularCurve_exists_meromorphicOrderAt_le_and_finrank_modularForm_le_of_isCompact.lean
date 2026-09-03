import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    ∃ C : ℕ, ∀ k : ℤ, 0 ≤ k →
      (∀ f : ModularForm Γ k, (f : ℍ → ℂ) ≠ 0 → ∀ τ : ℍ,
        meromorphicOrderAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ) ≤ (((C : ℤ) * k : ℤ) : WithTop ℤ)) ∧
      FiniteDimensional ℂ (ModularForm Γ k) ∧
      Module.finrank ℂ (ModularForm Γ k) ≤ C * k.toNat + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_meromorphicOrderAt_le_and_finrank_modularForm_le_of_isCompact.solution
