import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (P0 : Type u) [AddCommGroup P0] [Module (𝒱.cover c).A0 P0]
    [Module.Projective (𝒱.cover c).A0 P0] [Module.Finite (𝒱.cover c).A0 P0]
    (P1 : Type u) [AddCommGroup P1] [Module (𝒱.cover c).A1 P1]
    [Module.Projective (𝒱.cover c).A1 P1] [Module.Finite (𝒱.cover c).A1 P1]
    (hrk0 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] P0) = 1)
    (hrk1 : ∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] P1) = 1)
    (σ : letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
         letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
         ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0) ≃ₗ[(𝒱.cover c).A01]
           ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A1] P1)) :
    letI : Algebra (𝒱.cover c).A0 (𝒱.cover c).A01 := (𝒱.cover c).ρ0.toRingHom.toAlgebra
    letI : Algebra (𝒱.cover c).A1 (𝒱.cover c).A01 := (𝒱.cover c).ρ1.toRingHom.toAlgebra
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
      ∃ (e0 : (𝒱.sectionsOf c L).M0 ≃ₗ[(𝒱.cover c).A0] P0)
        (e1 : (𝒱.sectionsOf c L).M1 ≃ₗ[(𝒱.cover c).A1] P1)
        (e01 : (𝒱.sectionsOf c L).M01 ≃ₗ[(𝒱.cover c).A01]
          ((𝒱.cover c).A01 ⊗[(𝒱.cover c).A0] P0)),
        (∀ m, e01 ((𝒱.sectionsOf c L).r0 m) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A0] e0 m) ∧
        (∀ m, σ (e01 ((𝒱.sectionsOf c L).r1 m)) = (1 : (𝒱.cover c).A01) ⊗ₜ[(𝒱.cover c).A1] e1 m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective.solution
