import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_comp_eq_isPullback_levelIff_of_comp
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S₁ S₂ S₃ : Type} [CommRing S₁] [CommRing S₂] [CommRing S₃] (σ : S₁ →+* S₂) (τ : S₂ →+* S₃)
    (E₁ : FakeEllipticCurve Λ N S₁) (E₂ : FakeEllipticCurve Λ N S₂) (E₃ : FakeEllipticCurve Λ N S₃)
    (g : E₂.A ⟶ E₁.A) (hg : CategoryTheory.IsPullback g E₂.f E₁.f (Spec.map (CommRingCat.ofHom σ)))
    (h₁₂ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' E₂.f),
        (E₂.L.mul t' P Q).1 ≫ g =
          (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₂.act x ≫ g = g ≫ E₁.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' E₂.f),
        FactorsThrough E₂.lev P → ∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' E₂.f),
        (∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g) → FactorsThrough E₂.lev P))
    (g' : E₃.A ⟶ E₁.A) (hg' : CategoryTheory.IsPullback g' E₃.f E₁.f (Spec.map (CommRingCat.ofHom (τ.comp σ))))
    (h₁₃ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P Q : SchemeHomOver t' E₃.f),
        (E₃.L.mul t' P Q).1 ≫ g' =
          (E₁.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (τ.comp σ)))
            ⟨P.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g', by rw [Category.assoc, hg'.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₃.act x ≫ g' = g' ≫ E₁.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        FactorsThrough E₃.lev P → ∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g') ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        (∃ P₀ : T ⟶ E₁.C, P₀ ≫ E₁.lev = P.1 ≫ g') → FactorsThrough E₃.lev P)) :
    ∃ (h : E₃.A ⟶ E₂.A) (_ : h ≫ g = g') (hh : CategoryTheory.IsPullback h E₃.f E₂.f (Spec.map (CommRingCat.ofHom τ))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P Q : SchemeHomOver t' E₃.f),
        (E₃.L.mul t' P Q).1 ≫ h =
          (E₂.L.mul (t' ≫ Spec.map (CommRingCat.ofHom τ))
            ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E₃.act x ≫ h = h ≫ E₂.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        FactorsThrough E₃.lev P → ∃ P₀ : T ⟶ E₂.C, P₀ ≫ E₂.lev = P.1 ≫ h) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₃)) (P : SchemeHomOver t' E₃.f),
        (∃ P₀ : T ⟶ E₂.C, P₀ ≫ E₂.lev = P.1 ≫ h) → FactorsThrough E₃.lev P) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_comp_eq_isPullback_levelIff_of_comp.solution
