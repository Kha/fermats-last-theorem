import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_iso_of_isLevelIsogeny

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM
theorem CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_iso_of_isLevelIsogeny
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d : FakeEllipticCurve Λ N S)
    (huu' : FakeEllipticCurve.WithExtraLevel.Iso u u') (hd : FakeEllipticCurve.IsLevelIsogeny ℓ u' d) :
    FakeEllipticCurve.IsLevelIsogeny ℓ u d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_iso_of_isLevelIsogeny.solution
