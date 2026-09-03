import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (r : ℕ)
    (E E₁ : QM.FakeEllipticCurve Λ N S) (E' E₁' : QM.FakeEllipticCurve Λ N S')
    (hE : QM.FakeEllipticCurve.IsPullback φ E E') (hE₁ : QM.FakeEllipticCurve.IsPullback φ E₁ E₁')
    (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E₁) :
    QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E' E₁' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback.solution
