import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.existsUnique_isBaseScalar_of_isInvertible_of_bijective
    {X : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R => f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_DescentCharacter_existsUnique_isBaseScalar_of_isInvertible_of_bijective.solution
