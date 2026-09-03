import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq

open CategoryTheory AlgebraicGeometry NeronModelInfra
set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq
    {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} [IsSeparated f]
    (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
    (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ x.1 =
         Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ y.1) :
    x = y := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq.solution
