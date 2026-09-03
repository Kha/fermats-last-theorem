import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_iso_of_iso

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld QuaternionAlgebra

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.isAtkinLehnerQuotient_of_iso_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type u} [CommRing S] (r : ℕ)
    (u u' v v' : QM.FakeEllipticCurve.WithExtraLevel Λ N ℓ S)
    (h : QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r u u')
    (hu : QM.FakeEllipticCurve.WithExtraLevel.Iso u v) (hu' : QM.FakeEllipticCurve.WithExtraLevel.Iso u' v') :
    QM.FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient r v v' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_isAtkinLehnerQuotient_of_iso_of_iso.solution
