import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation
import P2M.Util
import P2M.Sol.S_WLight_span_inter_rational_of_twist_stable

set_option autoImplicit false
open Complex UpperHalfPlane Function
open scoped Topology Manifold ModularForm

theorem WLight.span_inter_rational_of_twist_stable (K : IntermediateField ℚ ℂ)
    (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (V : Submodule ℂ (ℍ → ℂ))
    (hVle : V ≤ Submodule.span ℂ (M : Set (ℍ → ℂ)))
    (hstab : ∀ (σ : ℂ ≃ₐ[↥K] ℂ) (v : ℍ → ℂ), v ∈ V →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) ∧
        v = ∑ w ∈ s, c w • w ∧ (∑ w ∈ s, σ (c w) • w) ∈ V)
    (G1 : ∀ c : ℂ, (∀ σ : ℂ ≃ₐ[↥K] ℂ, σ c = c) → ∃ a : ↥K, algebraMap ↥K ℂ a = c)
    {v : ℍ → ℂ} (hv : v ∈ V) :
    v ∈ Submodule.span ℂ {y : ℍ → ℂ | y ∈ V ∧ y ∈ M} := by p2m_exact_reverting @_root_.P2MW.S_WLight_span_inter_rational_of_twist_stable.solution
