import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_of_isPullback_comp_of_levelIff

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.isPullback_of_isPullback_comp_of_levelIff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {S₁ S₂ S₃ : Type} [CommRing S₁] [CommRing S₂] [CommRing S₃] (σ : S₁ →+* S₂) (τ : S₂ →+* S₃)
    (u₁ : FakeEllipticCurve.WithFullLevel Λ N m S₁) (u₂ : FakeEllipticCurve.WithFullLevel Λ N m S₂)
    (u₃ : FakeEllipticCurve.WithFullLevel Λ N m S₃)
    (g : u₂.1.A ⟶ u₁.1.A) (hg : CategoryTheory.IsPullback g u₂.1.f u₁.1.f (Spec.map (CommRingCat.ofHom σ)))
    (h₁₂ :
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t' u₂.1.f),
        (u₂.1.L.mul t' P Q).1 ≫ g =
          (u₁.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, u₂.1.act x ≫ g = g ≫ u₁.1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' u₂.1.f),
        FactorsThrough u₂.1.lev P → ∃ P₀ : T ⟶ u₁.1.C, P₀ ≫ u₁.1.lev = P.1 ≫ g) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₂)) (P : SchemeHomOver t' u₂.1.f),
        (∃ P₀ : T ⟶ u₁.1.C, P₀ ≫ u₁.1.lev = P.1 ≫ g) → FactorsThrough u₂.1.lev P) ∧
      (u₂.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom σ) ≫ (u₁.2.P).1)
    (h₁₃ : FakeEllipticCurve.WithFullLevel.IsPullback (τ.comp σ) u₁ u₃) :
    FakeEllipticCurve.WithFullLevel.IsPullback τ u₂ u₃ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_isPullback_of_isPullback_comp_of_levelIff.solution
