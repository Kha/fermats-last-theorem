import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.iso_of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (E : QM.FakeEllipticCurve Λ N S) (E' E'' : QM.FakeEllipticCurve Λ N S')
    (h' : QM.FakeEllipticCurve.IsPullback φ E E') (h'' : QM.FakeEllipticCurve.IsPullback φ E E'') :
    QM.FakeEllipticCurve.Iso E' E'' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_iso_of_isPullback_of_isPullback.solution
