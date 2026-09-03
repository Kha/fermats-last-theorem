import Definitions.Def_CerednikDrinfeld_QMModuliProps
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_transfer_forall_factorsThrough_iff
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (hℓℓ' : ℓ ≠ ℓ')
    (E E₁ : FakeEllipticCurve Λ N S) (K : E.ExtraLevel ℓ)
    (φ : E.A ⟶ E₁.A) (hφ : φ ≫ E₁.f = E.f) (ψ : E₁.A ⟶ E.A) (hψ : ψ ≫ E.f = E₁.f)
    (hφmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E₁.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hψmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      mapPt ψ hψ (E₁.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q))
    (hφact : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E₁.act x) (hψact : ∀ x : ↥Λ, E₁.act x ≫ ψ = ψ ≫ E.act x)
    (hφψ : ∀ hℓ : ((ℓ : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩ ∧ ψ ≫ φ = E₁.act ⟨((ℓ : ℚ) : ℍ[ℚ, a, b]), hℓ⟩)
    (hone : (1 : ℍ[ℚ, a, b]) ∈ Λ)
    (hker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      mapPt φ hφ P = E₁.L.one t ↔ FactorsThrough K.levK P)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough E.lev P → FactorsThrough E₁.lev (mapPt φ hφ P))
    (hlev' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E₁.f),
      FactorsThrough E₁.lev x → ∃ P : SchemeHomOver t E.f, FactorsThrough E.lev P ∧ mapPt φ hφ P = x) :

    (∀ K' : E.ExtraLevel ℓ', ∃ K₁' : E₁.ExtraLevel ℓ',
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t E₁.f),
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver t E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧

    (∀ K₁' : E₁.ExtraLevel ℓ', ∃ K' : E.ExtraLevel ℓ',
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
        FactorsThrough K₁'.levK x ↔ ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ∧

    (∀ K' K'' : E.ExtraLevel ℓ',
      (∀ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ↔ FactorsThrough K''.levK y) ↔
      (∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E₁.f,
          (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K'.levK y ∧ mapPt φ hφ y = x) ↔
          (∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f, FactorsThrough K''.levK y ∧ mapPt φ hφ y = x))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_transfer_forall_factorsThrough_iff.solution
