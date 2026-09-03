import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_hom_of_isPullback_algebraMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_hom_of_isPullback_algebraMap
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K']
    (𝒜₁ 𝒟₁ : FakeEllipticCurve Λ N ↥K') (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))
    (gE : E.A ⟶ 𝒜₁.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜₁.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜₁.act x)
    (gd : d.A ⟶ 𝒟₁.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟₁.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ)))))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟₁.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Kφ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥Kφ) (_ : K' ≤ Kφ),
      ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : Kφ ≤ K'')
        (j : ↥K' →+* ↥K'') (_ : ∀ x : ↥K', ((j x : ↥K'') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
        (𝒜₂ 𝒟₂ : FakeEllipticCurve Λ N ↥K'')
        (rE : E.A ⟶ 𝒜₂.A) (hrE : CategoryTheory.IsPullback rE E.f 𝒜₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))))
    (hrE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ rE =
        (𝒜₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rE, by rw [Category.assoc, hrE.w, ← Category.assoc, Q.2]⟩).1)
    (hrE_act : ∀ x : ↥Λ, E.act x ≫ rE = rE ≫ 𝒜₂.act x)
        (qE : 𝒜₂.A ⟶ 𝒜₁.A) (hqE : CategoryTheory.IsPullback qE 𝒜₂.f 𝒜₁.f (Spec.map (CommRingCat.ofHom (j))))
    (hqE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' 𝒜₂.f),
      (𝒜₂.L.mul t' P Q).1 ≫ qE =
        (𝒜₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (j)))
          ⟨P.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qE, by rw [Category.assoc, hqE.w, ← Category.assoc, Q.2]⟩).1)
    (hqE_act : ∀ x : ↥Λ, 𝒜₂.act x ≫ qE = qE ≫ 𝒜₁.act x)
        (_ : rE ≫ qE = gE)
        (rd : d.A ⟶ 𝒟₂.A) (hrd : CategoryTheory.IsPullback rd d.f 𝒟₂.f (Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ)))))
    (hrd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ rd =
        (𝒟₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥K'' (AlgebraicClosure ℚ))))
          ⟨P.1 ≫ rd, by rw [Category.assoc, hrd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ rd, by rw [Category.assoc, hrd.w, ← Category.assoc, Q.2]⟩).1)
    (hrd_act : ∀ x : ↥Λ, d.act x ≫ rd = rd ≫ 𝒟₂.act x)
        (qd : 𝒟₂.A ⟶ 𝒟₁.A) (hqd : CategoryTheory.IsPullback qd 𝒟₂.f 𝒟₁.f (Spec.map (CommRingCat.ofHom (j))))
    (hqd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t' 𝒟₂.f),
      (𝒟₂.L.mul t' P Q).1 ≫ qd =
        (𝒟₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (j)))
          ⟨P.1 ≫ qd, by rw [Category.assoc, hqd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ qd, by rw [Category.assoc, hqd.w, ← Category.assoc, Q.2]⟩).1)
    (hqd_act : ∀ x : ↥Λ, 𝒟₂.act x ≫ qd = qd ≫ 𝒟₁.act x)
        (_ : rd ≫ qd = gd),
        ∃ (φ₂ : 𝒜₂.A ⟶ 𝒟₂.A) (hφ₂ : φ₂ ≫ 𝒟₂.f = 𝒜₂.f),
          rE ≫ φ₂ = φ ≫ rd ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥K'')) (P Q : SchemeHomOver t 𝒜₂.f),
            mapPt φ₂ hφ₂ (𝒜₂.L.mul t P Q) = 𝒟₂.L.mul t (mapPt φ₂ hφ₂ P) (mapPt φ₂ hφ₂ Q)) ∧
          (∀ x : ↥Λ, 𝒜₂.act x ≫ φ₂ = φ₂ ≫ 𝒟₂.act x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_hom_of_isPullback_algebraMap.solution
