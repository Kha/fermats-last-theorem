import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_ProjSpace_isClosedImmersion_map_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (h : Function.Surjective (algebraMap R A)) (n : ℕ) :
    IsClosedImmersion (ProjSpace.map R A n) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A))) := IsClosedImmersion.spec_of_surjective _ h
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (ProjSpace.isPullback_map R A n).flip inferInstance
