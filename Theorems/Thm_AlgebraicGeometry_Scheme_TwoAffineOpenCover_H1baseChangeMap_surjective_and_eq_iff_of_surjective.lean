import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1baseChangeMap_surjective_and_eq_iff_of_surjective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A)) :
    Function.Surjective (𝒱.H1baseChangeMap c A) ∧
    ∀ x y : (𝒱.structureSheafSections c).H1,
      𝒱.H1baseChangeMap c A x = 𝒱.H1baseChangeMap c A y ↔
        x - y ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R (𝒱.structureSheafSections c).H1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective.solution
