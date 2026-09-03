import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (m ℓ : ℕ) (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S')
    (hu : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') :

    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k),
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ))) →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk'))) ∧

    (∀ (k : Type) [Field k] [IsAlgClosed k] (sk' : S' →+* k), (N : k) ≠ 0 →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk'))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk') (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk')) = u'.1.L.one (geomPoint k sk')) →
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ)))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k (sk'.comp φ)) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k (sk'.comp φ))) = u.1.L.one (geomPoint k (sk'.comp φ)))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_imp_eq_one_imp_and_imp_of_isPullback.solution
