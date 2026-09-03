import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_of_isLevelIsogeny_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) (d D : FakeEllipticCurve Λ N S)
    (hd : FakeEllipticCurve.IsLevelIsogeny ℓ u d) (h : FakeEllipticCurve.Iso d D) :
    FakeEllipticCurve.IsLevelIsogeny ℓ u D := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLevelIsogeny_of_isLevelIsogeny_of_iso.solution
