import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of R)) (P : X)
    {Ω : Type u} [Field Ω] [Algebra R Ω]
    (φ : X.residueField P ⟶ CommRingCat.of Ω)
    (hφ : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.appTop ≫ X.Γevaluation P ≫ φ =
      CommRingCat.ofHom (algebraMap R Ω)) :
    ∃ xη : Spec (CommRingCat.of Ω) ⟶ X,
      xη ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ∧
      xη.base (IsLocalRing.closedPoint Ω) = P := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_hom_spec_comp_eq_specMap_algebraMap_and_apply_eq_of_residueField.solution
