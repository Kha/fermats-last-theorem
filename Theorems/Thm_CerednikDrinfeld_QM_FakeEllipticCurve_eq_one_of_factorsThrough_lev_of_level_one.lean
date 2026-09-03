import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_factorsThrough_lev_of_level_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

universe u

open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.eq_one_of_factorsThrough_lev_of_level_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (hP : FactorsThrough E.lev P) :
    P = E.L.one t := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_eq_one_of_factorsThrough_lev_of_level_one.solution
