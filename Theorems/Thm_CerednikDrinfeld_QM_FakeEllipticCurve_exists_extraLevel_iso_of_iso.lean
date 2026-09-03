import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM
theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_iso_of_iso
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S] (ℓ : ℕ)
    (E E' : FakeEllipticCurve Λ N S) (h : FakeEllipticCurve.Iso E' E) (K' : E'.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      FakeEllipticCurve.WithExtraLevel.Iso (⟨E', K'⟩ : FakeEllipticCurve.WithExtraLevel Λ N ℓ S) ⟨E, K⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_iso_of_iso.solution
