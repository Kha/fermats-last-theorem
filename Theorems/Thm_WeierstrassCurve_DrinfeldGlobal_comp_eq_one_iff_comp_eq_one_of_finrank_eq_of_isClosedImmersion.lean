import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra
  WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T]
    (W₁ W₂ W₃ : WeierstrassCurve T) (hΔ₁ : IsUnit W₁.Δ) (hΔ₂ : IsUnit W₂.Δ) (hΔ₃ : IsUnit W₃.Δ)
    (f : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hf : f ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (g : projModelCR W₁.toProjective ⟶ projModelCR W₃.toProjective)
    (hg : g ≫ projModelStrCR W₃.toProjective = projModelStrCR W₁.toProjective)
    (hfhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ f, by rw [Category.assoc, hf]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) =
        (𝒢 T W₂ hΔ₂).mul t ⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ ⟨y.1 ≫ f, by rw [Category.assoc, hf]; exact y.2⟩)
    (hghom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) =
        (𝒢 T W₃ hΔ₃).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (m : ℕ) (hfrk : ∀ p, f.finrank p = m) (hgrk : ∀ p, g.finrank p = m)
    (K : Scheme) (ι : K ⟶ projModelCR W₁.toProjective) [IsClosedImmersion ι]
    [Flat (ι ≫ projModelStrCR W₁.toProjective)] [LocallyOfFinitePresentation (ι ≫ projModelStrCR W₁.toProjective)]
    (hKrk : ∀ s, (ι ≫ projModelStrCR W₁.toProjective).finrank s = m)
    (hKf : ι ≫ f = (ι ≫ projModelStrCR W₁.toProjective) ≫ ((𝒢 T W₂ hΔ₂).one (𝟙 _)).1)
    (hKg : ι ≫ g = (ι ≫ projModelStrCR W₁.toProjective) ≫ ((𝒢 T W₃ hΔ₃).one (𝟙 _)).1)
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W₁.toProjective)) :
    (⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) = (𝒢 T W₂ hΔ₂).one t ↔
      (⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) = (𝒢 T W₃ hΔ₃).one t := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_eq_one_iff_comp_eq_one_of_finrank_eq_of_isClosedImmersion.solution
