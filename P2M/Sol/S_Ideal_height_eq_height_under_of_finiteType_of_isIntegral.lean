import Mathlib
import Theorems.Thm_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
import P2M.Util
namespace P2MW.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral

set_option autoImplicit false

universe u

theorem solution
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] :
    q.height = (q.under A).height := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin d) k) A := g.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) k) B := ((algebraMap A B).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (MvPolynomial (Fin d) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ B).mpr
      ((FaithfulSMul.algebraMap_injective A B).comp hinj)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k) A := ⟨hint⟩
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k) B := Algebra.IsIntegral.trans A
  rw [Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) B q,
    Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) A
      (q.under A), Ideal.under_under]
