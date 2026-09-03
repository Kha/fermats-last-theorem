import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough E.lev P ↔ P = E.L.one t := by
  constructor
  · intro h
    have h1 := E.lev_torsion t P h
    change E.L.mul t (E.L.one t) P = E.L.one t at h1
    rwa [E.L.one_mul] at h1
  · rintro rfl
    exact E.lev_one t
