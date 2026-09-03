import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld.QM
open scoped Quaternion

open CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_isLevelIsogeny_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (ℓ : ℕ)
    (u : WithExtraLevel Λ N ℓ S) (𝒟 : FakeEllipticCurve Λ N S) (hud : IsLevelIsogeny ℓ u 𝒟)
    (Ā Dbar : FakeEllipticCurve Λ N S')

    (g : Ā.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g Ā.f u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hg_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Ā.f),
      (Ā.L.mul t' P Q).1 ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, Ā.act x ≫ g = g ≫ u.1.act x)
    (hg_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      FactorsThrough Ā.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g)
    (hg_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
      (∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) → FactorsThrough Ā.lev P)

    (h : Dbar.A ⟶ 𝒟.A) (hh : CategoryTheory.IsPullback h Dbar.f 𝒟.f (Spec.map (CommRingCat.ofHom φ)))
    (hh_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' Dbar.f),
      (Dbar.L.mul t' P Q).1 ≫ h =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1)
    (hh_act : ∀ x : ↥Λ, Dbar.act x ≫ h = h ≫ 𝒟.act x)
    (hh_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      FactorsThrough Dbar.lev P → ∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ h)
    (hh_lev' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Dbar.f),
      (∃ P₀ : T ⟶ 𝒟.C, P₀ ≫ 𝒟.lev = P.1 ≫ h) → FactorsThrough Dbar.lev P) :
    ∃ Kbar : Ā.ExtraLevel ℓ,

      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' Ā.f),
          FactorsThrough Kbar.levK P ↔ ∃ P₀ : T ⟶ u.2.K, P₀ ≫ u.2.levK = P.1 ≫ g) ∧
      IsLevelIsogeny ℓ (⟨Ā, Kbar⟩ : WithExtraLevel Λ N ℓ S') Dbar := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_isLevelIsogeny_of_isPullback.solution
