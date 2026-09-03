import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    {X' : AlgebraicGeometry.Scheme.{u}} (x' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of R'))
    (hsm : AlgebraicGeometry.Smooth x') (hsep : AlgebraicGeometry.IsSeparated x') (hqc : AlgebraicGeometry.QuasiCompact x')
    (hgc : AlgebraicGeometry.GeometricallyConnected x')
    (e : CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X')
    (he : e.hom ≫ x' = CategoryTheory.Limits.pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    AlgebraicGeometry.Smooth f ∧ AlgebraicGeometry.IsSeparated f ∧ AlgebraicGeometry.QuasiCompact f ∧
      AlgebraicGeometry.GeometricallyConnected f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange.solution
