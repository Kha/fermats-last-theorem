import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_QMRigidification
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (S : Type) [CommRing S] (E A : FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) :
    ∃ J : Ideal S, J.FG ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T)
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia ψ E E' gE)
        (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia ψ A A' gA)
        (φ' : E'.A ⟶ A'.A) (hφ' : φ' ≫ A'.f = E'.f),
        φ' ≫ gA = gE ≫ φ →
          (FakeEllipticCurve.PreservesLevel E' A' φ' hφ' ↔ J.map ψ = ⊥) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_ideal_fg_forall_preservesLevel_iff_map_eq_bot_of_isPullbackVia.solution
