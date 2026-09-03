import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} {S : Type u} [CommRing S]
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S) (c : ↥Λ) (h : FakeEllipticCurve.WithFullLevel.IsTwist c u u')
    (ℓ : ℕ) (hℓm : ℓ ∣ m) (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ)
    (hL₀c : ∀ x : ℍ[ℚ, a, b], x ∈ L₀ → x * (c : ℍ[ℚ, a, b]) ∈ L₀)
    (hsurj : ∀ y : ↥Λ, (y : ℍ[ℚ, a, b]) ∈ L₀ →
      ∃ x z : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ ∧ (y : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) + (ℓ : ℚ) • (z : ℍ[ℚ, a, b]))
    (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) :
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u'.1.lev
          (pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk))) →
        pushPt (u'.1.act x) (u'.1.act_over x)
            (nsmulPt u'.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u'.2.P k sk)) = u'.1.L.one (geomPoint k sk)) ↔
    (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        FactorsThrough u.1.lev
          (pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk))) →
        pushPt (u.1.act x) (u.1.act_over x)
            (nsmulPt u.1.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt u.2.P k sk)) = u.1.L.one (geomPoint k sk)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_forall_factorsThrough_lev_imp_eq_one_iff_of_isTwist.solution
