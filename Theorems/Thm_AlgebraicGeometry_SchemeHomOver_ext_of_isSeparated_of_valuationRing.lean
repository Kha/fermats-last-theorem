import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing

open CategoryTheory AlgebraicGeometry NeronModelInfra

universe u
set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.SchemeHomOver.ext_of_isSeparated_of_valuationRing
    {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f]
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
         Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_isSeparated_of_valuationRing.solution
