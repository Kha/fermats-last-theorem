import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

set_option autoImplicit false

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (rbc0 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01)
      (rbc1 : (𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1 ≃ₗ[(𝒱.cover c).A01]
                (𝒱.sectionsOf c M).M01),
      (∀ m, rbc0 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] m) = (𝒱.sectionsOf c M).r0 m) ∧
      (∀ m, rbc1 ((1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] m) = (𝒱.sectionsOf c M).r1 m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible.solution
