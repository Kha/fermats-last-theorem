import Definitions.Def_CerednikDrinfeld_QMModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_act_comp_of_quotients
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra NeronModelInfra GoodReductionJacobian
theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_act_comp_of_quotients
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k)
    (H₁ : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (C₁ : FakeEllipticCurve Λ N k) (p₁ : E.A ⟶ C₁.A) (hp₁ : p₁ ≫ C₁.f = E.f) (K₁ : Scheme.{0}) (κ₁ : K₁ ⟶ E.A)
    (hC₁ :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt p₁ hp₁ (E.L.mul t P Q) = C₁.L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p₁ = p₁ ≫ C₁.act x) ∧
      IsFinite p₁ ∧ Flat p₁ ∧ Surjective p₁ ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C₁.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, mapPt p₁ hp₁ P = R) ∧
      IsClosedImmersion κ₁ ∧ IsReduced K₁ ∧ IsFinite (κ₁ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough κ₁ P ↔ P ∈ H₁) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E.f),
        mapPt p₁ hp₁ Q = C₁.L.one t ↔ FactorsThrough κ₁ Q))
    (H₂ : Set (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f))
    (C₂ : FakeEllipticCurve Λ N k) (p₂ : E.A ⟶ C₂.A) (hp₂ : p₂ ≫ C₂.f = E.f) (K₂ : Scheme.{0}) (κ₂ : K₂ ⟶ E.A)
    (hC₂ :
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E.f),
        mapPt p₂ hp₂ (E.L.mul t P Q) = C₂.L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ p₂ = p₂ ≫ C₂.act x) ∧
      IsFinite p₂ ∧ Flat p₂ ∧ Surjective p₂ ∧
      (∀ R : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) C₂.f, ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, mapPt p₂ hp₂ P = R) ∧
      IsClosedImmersion κ₂ ∧ IsReduced K₂ ∧ IsFinite (κ₂ ≫ E.f) ∧
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f, FactorsThrough κ₂ P ↔ P ∈ H₂) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t E.f),
        mapPt p₂ hp₂ Q = C₂.L.one t ↔ FactorsThrough κ₂ Q))
    (m : ↥Λ) (hm : ∀ P, P ∈ H₁ → pushPt (E.act m) (E.act_over m) P ∈ H₂) :
    ∃ (θ : C₁.A ⟶ C₂.A) (hθ : θ ≫ C₂.f = C₁.f),
      p₁ ≫ θ = E.act m ≫ p₂ ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t C₁.f),
        mapPt θ hθ (C₁.L.mul t P Q) = C₂.L.mul t (mapPt θ hθ P) (mapPt θ hθ Q)) ∧
      (∀ θ' : C₁.A ⟶ C₂.A, θ' ≫ C₂.f = C₁.f → p₁ ≫ θ' = E.act m ≫ p₂ → θ' = θ) ∧
      (∀ x : ↥Λ, E.act m ≫ E.act x = E.act x ≫ E.act m →
        (∀ P, P ∈ H₁ → pushPt (E.act x) (E.act_over x) P ∈ H₁) →
          C₁.act x ≫ θ = θ ≫ C₂.act x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_act_comp_of_quotients.solution
