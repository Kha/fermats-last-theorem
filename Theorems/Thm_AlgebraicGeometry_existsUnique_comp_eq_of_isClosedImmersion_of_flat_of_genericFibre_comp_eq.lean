import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψK : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ Z)
    (hψK : ψK ≫ ι = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ) :
    ∃! ψ : X ⟶ Z, ψ ≫ ι = φ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq.solution
