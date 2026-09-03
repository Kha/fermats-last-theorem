import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_iso_of_iso

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_iso_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S] (r : ℕ)
    (E E' F F' : QM.FakeEllipticCurve Λ N S)
    (h : QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E')
    (hE : QM.FakeEllipticCurve.Iso E F) (hE' : QM.FakeEllipticCurve.Iso E' F') :
    QM.FakeEllipticCurve.IsAtkinLehnerQuotient r F F' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_iso_of_iso.solution
