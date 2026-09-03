import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
    {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] {f : 𝒞 ⟶ S} {r : ℕ}
    {X Y R : Scheme.{u}} [IsAffine X] [IsAffine Y] {gX : X ⟶ S} {gY : Y ⟶ S} {gR : R ⟶ S}
    (p : X ⟶ Y) (hp : p ≫ gY = gX)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (s t : R ⟶ X) (hs : s ≫ gX = gR) (ht : t ≫ gX = gR) (hR : IsPullback s t p p)
    (D : RelEffCartierDiv f r gX) (hD : D.pullbackAlong s hs = D.pullbackAlong t ht) :
    ∃! DY : RelEffCartierDiv f r gY, DY.pullbackAlong p hp = D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine.solution
