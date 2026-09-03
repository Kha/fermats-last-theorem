import Mathlib
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation
import P2M.Util
import P2M.Sol.S_Deformation_exists_residuallyTrivial_conj_of_conj

set_option autoImplicit false

universe u v
theorem Deformation.exists_residuallyTrivial_conj_of_conj
    {n : Type} [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    {k : Type u} [Field k] {A : Type v} [CommRing A] [IsLocalRing A]
    (π : A →+* k) (hπ : Function.Surjective π)
    (ρ₀ : G →* GL n k) [Representation.IsAbsolutelyIrreducible.{u} (Deformation.matrixRepresentation ρ₀)]
    (ρ₁ ρ₂ : G →* GL n A)
    (h₁ : ∀ g, ((ρ₁ g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (h₂ : ∀ g, ((ρ₂ g : GL n A) : Matrix n n A).map π = ((ρ₀ g : GL n k) : Matrix n n k))
    (g : GL n A) (hg : ∀ x, g * ρ₁ x * g⁻¹ = ρ₂ x) :
    ∃ γ : GL n A, ((γ : GL n A) : Matrix n n A).map π = 1 ∧ ∀ x, γ * ρ₁ x * γ⁻¹ = ρ₂ x := by p2m_exact_reverting @_root_.P2MW.S_Deformation_exists_residuallyTrivial_conj_of_conj.solution
