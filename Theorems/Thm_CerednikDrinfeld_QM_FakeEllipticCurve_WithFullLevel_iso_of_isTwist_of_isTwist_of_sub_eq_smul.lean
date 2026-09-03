import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_of_isTwist_of_isTwist_of_sub_eq_smul
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {N m : ℕ} {S : Type} [CommRing S]
    (u u' u'' : FakeEllipticCurve.WithFullLevel Λ N m S) (c c' : ↥Λ)
    (h' : FakeEllipticCurve.WithFullLevel.IsTwist c u u') (h'' : FakeEllipticCurve.WithFullLevel.IsTwist c' u u'')
    (hcc' : ∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) - (c' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    FakeEllipticCurve.WithFullLevel.Iso u' u'' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_iso_of_isTwist_of_isTwist_of_sub_eq_smul.solution
