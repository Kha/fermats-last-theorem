import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt_of_isIsogenyPair_pow_of_coprime_of_intCast_mem

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt_of_isIsogenyPair_pow_of_coprime_of_intCast_mem
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {N : ℕ} {S : Type u} [CommRing S] {m : ℕ}
    (E E' : FakeEllipticCurve Λ N S)
    (r d : ℕ) [Fact r.Prime] (hrm : Nat.Coprime r m)
    (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (ψ : E'.A ⟶ E.A)
    (hiso : FakeEllipticCurve.IsIsogenyPair (r ^ d) E E' φ ψ)
    (P : E.FullLevel m) :
    ∃ P' : E'.FullLevel m, P'.P = mapPt φ hφ P.P := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt_of_isIsogenyPair_pow_of_coprime_of_intCast_mem.solution
