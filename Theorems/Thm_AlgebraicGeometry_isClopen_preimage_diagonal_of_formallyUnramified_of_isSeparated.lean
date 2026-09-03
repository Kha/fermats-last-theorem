import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
    {Z S : Scheme.{u}} (p : Z ⟶ S) [FormallyUnramified p] [LocallyOfFiniteType p] [IsSeparated p]
    (σ τ : S ⟶ Z) (hσ : σ ≫ p = 𝟙 S) (hτ : τ ≫ p = 𝟙 S) :
    IsClopen ((pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : S.Opens) : Set S) ∧
    ∀ {T : Scheme.{u}} (g : T ⟶ S),
      Set.range g ⊆ (pullback.lift σ τ (hσ.trans hτ.symm) ⁻¹ᵁ (pullback.diagonal p).opensRange : Set S) ↔ g ≫ σ = g ≫ τ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated.solution
