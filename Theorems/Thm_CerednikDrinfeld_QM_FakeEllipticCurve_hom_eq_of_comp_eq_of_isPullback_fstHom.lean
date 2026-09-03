import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_hom_eq_of_comp_eq_of_isPullback_fstHom
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory open AlgebraicGeometry hiding bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected open NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
open scoped Quaternion

universe u

theorem CerednikDrinfeld.QM.FakeEllipticCurve.hom_eq_of_comp_eq_of_isPullback_fstHom
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {k : Type u} [Field k] (E : FakeEllipticCurve Λ N k) (t t' : FakeEllipticCurve Λ N (DualNumber k))
    (g : E.A ⟶ t.A)
    (hg : CategoryTheory.IsPullback g E.f t.f
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)))
    (e₁ e₂ : t.A ⟶ t'.A) (he₁ : e₁ ≫ t'.f = t.f) (he₂ : e₂ ≫ t'.f = t.f)
    (hom₁ : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t'' t.f),
      mapPt e₁ he₁ (t.L.mul t'' P Q) = t'.L.mul t'' (mapPt e₁ he₁ P) (mapPt e₁ he₁ Q))
    (hom₂ : ∀ {T : Scheme.{u}} (t'' : T ⟶ Spec (CommRingCat.of (DualNumber k))) (P Q : SchemeHomOver t'' t.f),
      mapPt e₂ he₂ (t.L.mul t'' P Q) = t'.L.mul t'' (mapPt e₂ he₂ P) (mapPt e₂ he₂ Q))
    (h : g ≫ e₁ = g ≫ e₂) : e₁ = e₂ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_hom_eq_of_comp_eq_of_isPullback_fstHom.solution
