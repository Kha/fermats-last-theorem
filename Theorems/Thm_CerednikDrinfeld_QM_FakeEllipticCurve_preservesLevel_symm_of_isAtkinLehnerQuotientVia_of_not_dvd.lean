import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian
theorem CerednikDrinfeld.QM.FakeEllipticCurve.preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (r : ℕ) [Fact r.Prime] (hrN : ¬ r ∣ N)
    {S : Type} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (q : E.A ⟶ E'.A) (hq : q ≫ E'.f = E.f) (q' : E'.A ⟶ E.A) (hq' : q' ≫ E.f = E'.f)
    (h : FakeEllipticCurve.IsAtkinLehnerQuotientVia r E E' q hq q' hq') :
    FakeEllipticCurve.PreservesLevel E' E q' hq' := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_preservesLevel_symm_of_isAtkinLehnerQuotientVia_of_not_dvd.solution
