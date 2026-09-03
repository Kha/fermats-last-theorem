import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_factorsThrough_lev_of_level_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (hP : FactorsThrough E.lev P) :
    P = E.L.one t := by
  have h := E.lev_torsion t P hP

  rw [show nsmulPt E.L t 1 P = E.L.mul t (E.L.one t) P from rfl, E.L.one_mul] at h
  exact h
