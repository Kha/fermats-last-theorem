import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassProjModel NeronModelInfra
  WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (B : Type) [CommRing B] [Algebra A B] (V : WeierstrassCurve B) (hΔ : IsUnit V.Δ)
    (k : Type) [Field k] [CharP k q] (β : B →+* DualNumber k)
    (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom β)) (projModelStrCR V))
    (hQq : (𝒢 B V hΔ).nsmul _ q Q = (𝒢 B V hΔ).one _)
    (hQ0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ Q.1 ≠
      ((𝒢 B V hΔ).one (Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.fstHom k k k).toRingHom.comp β)))).1)
    [Algebra A (DualNumber k)] [CharP (DualNumber k) q]
    (hΔW : IsUnit (V.map β).Δ) (hΔq : IsUnit ((V.map β).map (frobenius (DualNumber k) q)).Δ)
    (Φ : projModelCR (V.map β).toProjective ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective = projModelStrCR (V.map β).toProjective)
    (hZ : ∃ ψ : ZChartRing ((V.map β).map (frobenius (DualNumber k) q)).toProjective →+* ZChartRing (V.map β).toProjective,
        ψ (xOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = xOverZ (V.map β).toProjective ^ q ∧
        ψ (yOverZ ((V.map β).map (frobenius (DualNumber k) q)).toProjective) = yOverZ (V.map β).toProjective ^ q ∧
        zChartι (V.map β).toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hΦhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR (V.map β).toProjective)),
      (⟨((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).1 ≫ Φ, by rw [Category.assoc, hΦ]; exact ((𝒢 (DualNumber k) (V.map β) hΔW).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)) =
        (𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t ⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ ⟨y.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact y.2⟩)

    (Vq : projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective ⟶ projModelCR (V.map β).toProjective)
    (hV : Vq ≫ projModelStrCR (V.map β).toProjective = projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hVq : Φ ≫ Vq = (𝒢 (DualNumber k) (V.map β) hΔW).schemeNsmul q)

    (W₃ : WeierstrassCurve (DualNumber k)) (hΔ₃ : IsUnit W₃.Δ)
    (g : projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective ⟶ projModelCR W₃.toProjective)
    (hg : g ≫ projModelStrCR W₃.toProjective = projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)
    (hghom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective)),
      (⟨((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 (DualNumber k) ((V.map β).map (frobenius (DualNumber k) q)) hΔq).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) =
        (𝒢 (DualNumber k) W₃ hΔ₃).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩)
    (hK : ∀ (P : Section ((V.map β).map (frobenius (DualNumber k) q)).toProjective) (x₀ y₀ : k),
      IsSectionThrough P (algebraMap k (DualNumber k) x₀) (algebraMap k (DualNumber k) y₀) →
      P.1 ≫ Vq = (kwZeroSect (DualNumber k) (V.map β)).1 →
      P.1 ≫ g = (kwZeroSect (DualNumber k) W₃).1) :
    ∃ (K : Scheme) (ι : K ⟶ projModelCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective),
      IsClosedImmersion ι ∧
      Flat (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ∧
      LocallyOfFinitePresentation (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ∧
      (∀ s, (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective).finrank s = q) ∧
      ι ≫ Vq = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫
        ((𝒢 (DualNumber k) (V.map β) hΔW).one (𝟙 _)).1 ∧
      ι ≫ g = (ι ≫ projModelStrCR ((V.map β).map (frobenius (DualNumber k) q)).toProjective) ≫
        ((𝒢 (DualNumber k) W₃ hΔ₃).one (𝟙 _)).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_comp_eq_comp_one_of_comp_eq_schemeNsmul_of_nsmul_eq_one.solution
