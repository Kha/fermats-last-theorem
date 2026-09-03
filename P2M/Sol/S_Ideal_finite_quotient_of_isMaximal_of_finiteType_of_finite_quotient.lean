import Mathlib
import P2M.Util
namespace P2MW.S_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient

set_option autoImplicit false

theorem solution
    (A : Type) [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal] [Finite (A ⧸ 𝔪)]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔪 : Ideal.map (algebraMap A B) 𝔪 ≤ 𝔭) :
    Finite (B ⧸ 𝔭) := by
  classical
  letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  letI : Field (B ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hle : 𝔪 ≤ 𝔭.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.mp h𝔪
  let f : A ⧸ 𝔪 →+* B ⧸ 𝔭 := Ideal.quotientMap 𝔭 (algebraMap A B) hle
  letI : Algebra (A ⧸ 𝔪) (B ⧸ 𝔭) := f.toAlgebra
  haveI : IsScalarTower A (A ⧸ 𝔪) (B ⧸ 𝔭) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.FiniteType A (B ⧸ 𝔭) := inferInstance
  haveI : Algebra.FiniteType (A ⧸ 𝔪) (B ⧸ 𝔭) := Algebra.FiniteType.of_restrictScalars_finiteType A _ _
  haveI : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔭) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Module.finite_of_finite (A ⧸ 𝔪)
