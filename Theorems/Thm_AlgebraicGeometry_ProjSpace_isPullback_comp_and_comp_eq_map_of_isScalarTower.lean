import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.isPullback_comp_and_comp_eq_map_of_isScalarTower
    {A : Type u} [CommRing A] (B C : Type u) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] {n : ℕ}
    {Z ZB ZC : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) (ιB : ZB ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (ιC : ZC ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C))
    (e : ZB ⟶ Z) (f : ZC ⟶ ZB)
    (hpb : IsPullback e (ιB ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hcomp : e ≫ ι = ιB ≫ ProjSpace.map A B n)
    (hpb' : IsPullback f (ιC ≫ ProjSpace.π C n) (ιB ≫ ProjSpace.π B n) (Spec.map (CommRingCat.ofHom (algebraMap B C))))
    (hcomp' : f ≫ ιB = ιC ≫ ProjSpace.map B C n) :
    IsPullback (f ≫ e) (ιC ≫ ProjSpace.π C n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A C))) ∧
    (f ≫ e) ≫ ι = ιC ≫ ProjSpace.map A C n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower.solution
