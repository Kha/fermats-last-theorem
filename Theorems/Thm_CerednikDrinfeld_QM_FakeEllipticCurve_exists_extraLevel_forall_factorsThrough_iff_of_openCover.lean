import Definitions.Def_CerednikDrinfeld_QMFineModuli
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover

set_option autoImplicit false

universe u

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_of_openCover
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (n : ℕ)
    {ι : Type u} (Sᵢ : ι → Type u) [∀ i, CommRing (Sᵢ i)] (φ : ∀ i, S →+* Sᵢ i)
    (hopen : ∀ i, IsOpenImmersion (Spec.map (CommRingCat.ofHom (φ i))))
    (hcover : ∀ x : ↥(Spec (CommRingCat.of S)), ∃ i, x ∈ Set.range (Spec.map (CommRingCat.ofHom (φ i))).base)
    (Eᵢ : ∀ i, FakeEllipticCurve Λ N (Sᵢ i))
    (g : ∀ i, (Eᵢ i).A ⟶ E.A)
    (hg : ∀ i, CategoryTheory.IsPullback (g i) (Eᵢ i).f E.f (Spec.map (CommRingCat.ofHom (φ i))))
    (hg_mul : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P Q : SchemeHomOver t (Eᵢ i).f),
      ((Eᵢ i).L.mul t P Q).1 ≫ g i =
        (E.L.mul (t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ (i : ι) (x : ↥Λ), (Eᵢ i).act x ≫ g i = g i ≫ E.act x)
    (hg_lev : ∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
      FactorsThrough E.lev (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
          ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ →
        FactorsThrough (Eᵢ i).lev P)
    (K : ∀ i, (Eᵢ i).ExtraLevel n)
    (hK : ∀ (i j : ι) {T : Scheme.{u}}
      (tᵢ : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (tⱼ : T ⟶ Spec (CommRingCat.of (Sᵢ j)))
      (Pᵢ : SchemeHomOver tᵢ (Eᵢ i).f) (Pⱼ : SchemeHomOver tⱼ (Eᵢ j).f),
      Pᵢ.1 ≫ g i = Pⱼ.1 ≫ g j → (FactorsThrough (K i).levK Pᵢ ↔ FactorsThrough (K j).levK Pⱼ)) :
    ∃ K₀ : E.ExtraLevel n,
      (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
        FactorsThrough K₀.levK (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
            ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
          FactorsThrough (K i).levK P) ∧
      (∀ K₁ : E.ExtraLevel n,
        (∀ (i : ι) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Sᵢ i))) (P : SchemeHomOver t (Eᵢ i).f),
          FactorsThrough K₁.levK (t := t ≫ Spec.map (CommRingCat.ofHom (φ i)))
              ⟨P.1 ≫ g i, by rw [Category.assoc, (hg i).w, ← Category.assoc, P.2]⟩ ↔
            FactorsThrough (K i).levK P) →
        ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
          FactorsThrough K₁.levK P ↔ FactorsThrough K₀.levK P) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_of_openCover.solution
