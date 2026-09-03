import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_comp_of_isPullback_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.isPullback_comp_of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S₀ S₁ S₂ : Type u} [CommRing S₀] [CommRing S₁] [CommRing S₂]
    (j : S₀ →+* S₁) (ι : S₁ →+* S₂)
    (E₀ : FakeEllipticCurve Λ N S₀) (E₁ : FakeEllipticCurve Λ N S₁) (E₂ : FakeEllipticCurve Λ N S₂)
    (h₀₁ : FakeEllipticCurve.IsPullback j E₀ E₁) (h₁₂ : FakeEllipticCurve.IsPullback ι E₁ E₂) :
    FakeEllipticCurve.IsPullback (ι.comp j) E₀ E₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isPullback_comp_of_isPullback_of_isPullback.solution
