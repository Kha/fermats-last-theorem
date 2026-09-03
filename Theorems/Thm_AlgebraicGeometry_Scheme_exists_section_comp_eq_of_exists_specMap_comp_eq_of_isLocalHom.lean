import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))

    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (K' : Type u) [Field K'] [Algebra R' K'] [Algebra K K']
    (y : Spec (CommRingCat.of R') ⟶ X) (hy : y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (hxy : Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ x = Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ y) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom.solution
