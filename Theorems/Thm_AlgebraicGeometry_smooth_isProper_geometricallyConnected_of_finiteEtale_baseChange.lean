import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of R'))
    (hsm : Smooth x') (hpr : IsProper x') (hgc : GeometricallyConnected x')
    (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X')
    (he : e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Smooth f ∧ IsProper f ∧ GeometricallyConnected f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange.solution
