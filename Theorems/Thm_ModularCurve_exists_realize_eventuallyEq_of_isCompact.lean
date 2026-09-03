import Definitions.Def_ModularCurve_AutomorphicField
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_realize_eventuallyEq_of_isCompact
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    [hdisc : DiscreteTopology ↥Γ]
    (hcpt : ∃ K : Set ℍ, IsCompact K ∧ ∀ τ : ℍ, ∃ γ ∈ Γ, γ • τ ∈ K)
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (hample : ∀ (S : Finset ℍ) (n : ℍ → ℕ),
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ P : ModularForm Γ k, (P : ℍ → ℂ) ≠ 0 ∧
        ∀ τ ∈ S, ((n τ : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z : ℂ => P (ofComplex z)) (τ : ℂ))
    (f : ℍ → ℂ) (hf : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => f (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, f (γ • z) = f z) :
    ∃ x : ↥(ModularCurve.automorphicField Γ),
      ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ, ModularCurve.automorphicField.realize x z = f z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_realize_eventuallyEq_of_isCompact.solution
