import Mathlib
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Definitions.Def_RingTheory_AffineDilatation
import P2M.Util
import P2M.Sol.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed"

universe u

theorem NeronModelInfra.exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (t : ℕ) (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hanti : ∀ i, Y (i + 1) ⊆ Y i) (hYt : Y t = ∅)
    (hYs : ∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType v ∧ QuasiCompact v ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ ⟨(Y 0)ᶜ, (hY 0).isOpen_compl⟩) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
        Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃! x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f), x₁.1 ≫ v = x.1) ∧
      (∀ (i : ℕ), i < t → ∀ (U : X.Opens) (hU : IsAffineOpen U), (∀ y ∈ (U : Set X), y ∉ Y (i + 1)) →
        ∀ (π : R), IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ (W : X₁.Opens)
          (e : (W : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))),
          W.ι ≫ v = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec ∧
          ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
            Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
            ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ Y i →
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ U →
              x₁.1 (IsLocalRing.closedPoint R') ∈ W) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed.solution
