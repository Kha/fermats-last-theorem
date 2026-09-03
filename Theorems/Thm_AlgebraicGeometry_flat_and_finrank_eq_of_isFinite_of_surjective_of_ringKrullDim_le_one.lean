import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdim : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1)

    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] (d : ℕ)
    (hd : letI : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.appLE U (π ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      Module.finrank Y.functionField (Y.functionField ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)) = d) :
    ∃ (_ : LocallyOfFinitePresentation π), Flat π ∧ ∀ y : Y, π.finrank y = d := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_flat_and_finrank_eq_of_isFinite_of_surjective_of_ringKrullDim_le_one.solution
