import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {B : Type} [CommRing B] {E Ef : FakeEllipticCurve Λ N B} {d : ℕ}
    (q : E.A ⟶ Ef.A) (q' : Ef.A ⟶ E.A) (hqq' : FakeEllipticCurve.IsIsogenyPair d E Ef q q')
    {L : Type} [CommRing L] (φ : B →+* L)
    {EL EfL : FakeEllipticCurve Λ N L}
    (g : EL.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia φ E EL g)
    (gf : EfL.A ⟶ Ef.A) (hgf : FakeEllipticCurve.IsPullbackVia φ Ef EfL gf) :
    ∃ (qL : EL.A ⟶ EfL.A) (qL' : EfL.A ⟶ EL.A), qL ≫ gf = g ≫ q ∧ qL' ≫ g = gf ≫ q' ∧
      FakeEllipticCurve.IsIsogenyPair d EL EfL qL qL' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isIsogenyPair_comp_eq_of_isPullbackVia_of_isPullbackVia.solution
