import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback

set_option autoImplicit false

universe u

open scoped Quaternion
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_equiv_schemeHomOver_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S S' : Type u} [CommRing S] [CommRing S']
    (φ : S →+* S') (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S')
    (g : E'.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E'.f E.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t E'.f),
      (E'.L.mul t P Q).1 ≫ g =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E'.act x ≫ g = g ≫ E.act x)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S')) :
    ∃ σ : SchemeHomOver t E'.f ≃ SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom φ)) E.f,
      (∀ P : SchemeHomOver t E'.f, (σ P).1 = P.1 ≫ g) ∧
      σ (E'.L.one t) = E.L.one _ ∧
      (∀ P Q : SchemeHomOver t E'.f, σ (E'.L.mul t P Q) = E.L.mul _ (σ P) (σ Q)) ∧
      (∀ P : SchemeHomOver t E'.f, σ (E'.L.inv t P) = E.L.inv _ (σ P)) ∧
      (∀ (n : ℕ) (P : SchemeHomOver t E'.f), σ (nsmulPt E'.L t n P) = nsmulPt E.L _ n (σ P)) ∧
      (∀ (x : ↥Λ) (P : SchemeHomOver t E'.f),
        σ (pushPt (E'.act x) (E'.act_over x) P) = pushPt (E.act x) (E.act_over x) (σ P)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_equiv_schemeHomOver_of_isPullback.solution
