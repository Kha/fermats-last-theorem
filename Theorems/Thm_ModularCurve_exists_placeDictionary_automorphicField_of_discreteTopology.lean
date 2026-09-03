import Definitions.Def_ModularCurve_AutomorphicField
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.Analysis.Meromorphic.Order
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_placeDictionary_automorphicField_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne]
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ]
    (hsep : ∀ τ σ : ℍ, (∀ γ ∈ Γ, γ • τ ≠ σ) →
      ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, g τ * h σ ≠ g σ * h τ)
    (hloc : ∀ τ : ℍ, ∃ k : ℤ, 4 ≤ k ∧ Even k ∧ ∃ g h : ModularForm Γ k, h τ ≠ 0 ∧
      meromorphicOrderAt (fun z : ℂ => g (ofComplex z) / h (ofComplex z)) (τ : ℂ) =
        (((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) : WithTop ℤ)) :
    ∃ pt : ℍ → AlgebraicCurve.Place ℂ ↥(ModularCurve.automorphicField Γ),
      (∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ∈ (pt τ).toValuationSubring ↔
        Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
          (fun z : ℍ => ‖ModularCurve.automorphicField.realize x z‖)) ∧
      (∀ (τ : ℍ) (x : ↥(ModularCurve.automorphicField Γ)), x ≠ 0 →
        meromorphicOrderAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ) =
          ((((Nat.card (MulAction.stabilizer Γ τ) / 2 : ℕ) : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)) ∧
      (∀ τ τ' : ℍ, pt τ = pt τ' ↔ ∃ γ ∈ Γ, γ • τ = τ') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_placeDictionary_automorphicField_of_discreteTopology.solution
