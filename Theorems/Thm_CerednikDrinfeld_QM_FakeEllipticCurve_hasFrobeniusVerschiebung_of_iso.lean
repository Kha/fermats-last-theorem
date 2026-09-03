import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hasFrobeniusVerschiebung_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ]
    (d d' E : FakeEllipticCurve Λ N S)
    (hD : HasFrobeniusVerschiebung ℓ d d') (he : FakeEllipticCurve.Iso d' E) :
    HasFrobeniusVerschiebung ℓ d E := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_hasFrobeniusVerschiebung_of_iso.solution
