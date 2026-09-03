import Mathlib.NumberTheory.ModularForms.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_modularForm_eq_const_and_eq_zero_of_isCompact

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.modularForm_eq_const_and_eq_zero_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K) :
    (∀ f : ModularForm Γ 0, ∃ c : ℂ, (f : ℍ → ℂ) = fun _ => c) ∧
    (∀ k : ℤ, k < 0 → ∀ f : ModularForm Γ k, (f : ℍ → ℂ) = 0) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularForm_eq_const_and_eq_zero_of_isCompact.solution
