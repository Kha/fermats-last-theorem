import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_iff_of_isPullback

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.generates_annihilator_iff_of_isPullback
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ)
    (R' L : Type) [CommRing R'] [CommRing L] (φ : R' →+* L)
    (E' : FakeEllipticCurve Λ N R') (P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) E'.f)
    (E : FakeEllipticCurve Λ N L) (gL : E.A ⟶ E'.A)
    (hgL : CategoryTheory.IsPullback gL E.f E'.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ gL =
          (E'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gL, by rw [Category.assoc, hgL.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E.act x ≫ gL = gL ≫ E'.act x)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) E.f) (hP : P.1 ≫ gL = Spec.map (CommRingCat.ofHom φ) ≫ P'.1)
    (k : Type) [Field k] [IsAlgClosed k] (sk : L →+* k) :
    ((∀ Q : SchemeHomOver (geomPoint k sk) E.f,
        nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
          ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = Q) ∧
     (∀ x : ↥Λ, pushPt (E.act x) (E.act_over x) (FakeEllipticCurve.sectionAt P k sk) = E.L.one (geomPoint k sk) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))) ↔
    ((∀ Q : SchemeHomOver (geomPoint k (sk.comp φ)) E'.f,
        nsmulPt E'.L (geomPoint k (sk.comp φ)) m Q = E'.L.one (geomPoint k (sk.comp φ)) →
          ∃ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k (sk.comp φ)) = Q) ∧
     (∀ x : ↥Λ, pushPt (E'.act x) (E'.act_over x) (FakeEllipticCurve.sectionAt P' k (sk.comp φ)) = E'.L.one (geomPoint k (sk.comp φ)) ↔
        ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_generates_annihilator_iff_of_isPullback.solution
