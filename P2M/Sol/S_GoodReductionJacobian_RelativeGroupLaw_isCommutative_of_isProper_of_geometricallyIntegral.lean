import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isCommutative_of_isProper_of_geometricallyIntegral

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f]
    [GeometricallyIntegral f] (G : RelativeGroupLaw K f) : G.IsCommutative :=
  fun {_} t x y => G.mul_comm_of_isProper_of_geometricallyIntegral t x y
