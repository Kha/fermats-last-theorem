import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isLocallyConstant_finrank_one
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] :
    (∀ y : ↥A.A, φ.finrank y =
        φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base (A.f.base y))) ∧
      IsLocallyConstant (fun s : ↥(Spec (CommRingCat.of S)) =>
        φ.finrank ((A.L.one (𝟙 (Spec (CommRingCat.of S)))).1.base s)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isLocallyConstant_finrank_one.solution
