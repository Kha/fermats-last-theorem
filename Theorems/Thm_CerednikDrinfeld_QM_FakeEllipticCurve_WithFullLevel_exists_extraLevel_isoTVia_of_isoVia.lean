import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_extraLevel_isoTVia_of_isoVia

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_extraLevel_isoTVia_of_isoVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {S : Type} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f)
    (hiso : FakeEllipticCurve.WithFullLevel.IsoVia u u' e he) (ℓ : ℕ) (C' : u'.1.ExtraLevel ℓ) :
    ∃ C : u.1.ExtraLevel ℓ, FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' e he := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_extraLevel_isoTVia_of_isoVia.solution
