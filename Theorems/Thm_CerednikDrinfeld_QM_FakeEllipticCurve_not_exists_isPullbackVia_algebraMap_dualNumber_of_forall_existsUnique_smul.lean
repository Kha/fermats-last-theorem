import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (k : Type) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (hqq'u : IsUnit ((q * q' : ℕ) : k))
    (u : FakeEllipticCurve Λ 1 k)
    (v : FakeEllipticCurve Λ 1 (DualNumber k)) (gv : u.A ⟶ v.A)
    (hv : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom v u gv)
    (hgen : ∀ (t : FakeEllipticCurve Λ 1 (DualNumber k)) (gt : u.A ⟶ t.A),
        FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom t u gt →
        (∃ c : k, ∀ (w : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A) (hw : w.A ⟶ v.A),
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w hw →
          gw ≫ hw = gv →
          ∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw) ∧
        (∀ (c c' : k) (w w' : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A) (gw' : u.A ⟶ w'.A)
          (hw : w.A ⟶ v.A) (hw' : w'.A ⟶ v.A),
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom v w hw →
          gw ≫ hw = gv →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w' u gw' →
          FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.map (R' := k) (c' • (LinearMap.id : k →ₗ[k] k))).toRingHom v w' hw' →
          gw' ≫ hw' = gv →
          (∃ h : t.A ⟶ w.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w t h ∧ gt ≫ h = gw) →
          (∃ h' : t.A ⟶ w'.A, FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) w' t h' ∧ gt ≫ h' = gw') →
          c = c'))
    (w : FakeEllipticCurve Λ 1 (DualNumber k)) (gw : u.A ⟶ w.A)
    (hw : FakeEllipticCurve.IsPullbackVia (TrivSqZeroExt.fstHom k k k).toRingHom w u gw)
    (h : w.A ⟶ v.A) (hh : FakeEllipticCurve.IsPullbackVia (RingHom.id (DualNumber k)) v w h) (hgwh : gw ≫ h = gv) :
    ¬ ∃ h₀ : w.A ⟶ u.A,
        FakeEllipticCurve.IsPullbackVia (algebraMap k (DualNumber k)) u w h₀ ∧ gw ≫ h₀ = 𝟙 u.A := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_not_exists_isPullbackVia_algebraMap_dualNumber_of_forall_existsUnique_smul.solution
