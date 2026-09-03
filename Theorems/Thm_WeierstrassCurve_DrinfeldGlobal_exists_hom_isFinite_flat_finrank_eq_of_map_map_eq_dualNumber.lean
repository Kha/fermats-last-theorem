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
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] [Algebra A (DualNumber k)] [CharP (DualNumber k) q]
    (W Wq : WeierstrassCurve (DualNumber k)) (hΔW : IsUnit W.Δ) (hΔq : IsUnit Wq.Δ)
    (Wq₀ : WeierstrassCurve k) (hconst : Wq₀.map (algebraMap k (DualNumber k)) = Wq)
    (W₀ : WeierstrassCurve k) (hW₀ : W.map (TrivSqZeroExt.fstHom k k k).toRingHom = W₀)
    (hΔ₀ : IsUnit (W₀.map (algebraMap k (DualNumber k))).Δ)
    (Vq : projModelCR Wq.toProjective ⟶ projModelCR W.toProjective)
    (hV : Vq ≫ projModelStrCR W.toProjective = projModelStrCR Wq.toProjective)
    (hVhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR Wq.toProjective)),
      (⟨((𝒢 (DualNumber k) Wq hΔq).mul t x y).1 ≫ Vq, by rw [Category.assoc, hV]; exact ((𝒢 (DualNumber k) Wq hΔq).mul t x y).2⟩ :
          SchemeHomOver t (projModelStrCR W.toProjective)) =
        (𝒢 (DualNumber k) W hΔW).mul t ⟨x.1 ≫ Vq, by rw [Category.assoc, hV]; exact x.2⟩ ⟨y.1 ≫ Vq, by rw [Category.assoc, hV]; exact y.2⟩)
    [IsFinite Vq] [Flat Vq] [LocallyOfFinitePresentation Vq] [Surjective Vq]
    (m : ℕ) (hVrk : ∀ p, Vq.finrank p = m)
    (hVO : (kwZeroSect (DualNumber k) Wq).1 ≫ Vq = (kwZeroSect (DualNumber k) W).1) :
    ∃ g : projModelCR Wq.toProjective ⟶ projModelCR (W₀.map (algebraMap k (DualNumber k))).toProjective,
      ∃ hg : g ≫ projModelStrCR (W₀.map (algebraMap k (DualNumber k))).toProjective = projModelStrCR Wq.toProjective,
      (∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of (DualNumber k))) (x y : SchemeHomOver t (projModelStrCR Wq.toProjective)),
        (⟨((𝒢 (DualNumber k) Wq hΔq).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 (DualNumber k) Wq hΔq).mul t x y).2⟩ :
            SchemeHomOver t (projModelStrCR (W₀.map (algebraMap k (DualNumber k))).toProjective)) =
          (𝒢 (DualNumber k) (W₀.map (algebraMap k (DualNumber k))) hΔ₀).mul t
            ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩) ∧
      IsFinite g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧
      (∀ p, g.finrank p = m) ∧
      (kwZeroSect (DualNumber k) Wq).1 ≫ g = (kwZeroSect (DualNumber k) (W₀.map (algebraMap k (DualNumber k)))).1 ∧
      (∀ (P : Section Wq.toProjective) (x₀ y₀ : k),
        IsSectionThrough P (algebraMap k (DualNumber k) x₀) (algebraMap k (DualNumber k) y₀) →
        P.1 ≫ Vq = (kwZeroSect (DualNumber k) W).1 →
        P.1 ≫ g = (kwZeroSect (DualNumber k) (W₀.map (algebraMap k (DualNumber k)))).1) ∧
      (∀ (φ : projModelGradingCR W.toProjective →+*ᵍ
            projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective)
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map φ)
        (_ : IsCoefficientHom W.toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ)
        (φ' : projModelGradingCR (W₀.map (algebraMap k (DualNumber k))).toProjective →+*ᵍ
            projModelGradingCR (((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)).toProjective)
        (hφ' : HomogeneousIdeal.irrelevant
            (projModelGradingCR (((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom)).toProjective) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR (W₀.map (algebraMap k (DualNumber k))).toProjective)).map φ')
        (_ : IsCoefficientHom (W₀.map (algebraMap k (DualNumber k))).toProjective (TrivSqZeroExt.fstHom k k k).toRingHom φ')
        (hW' : ((W₀.map (algebraMap k (DualNumber k))).map (TrivSqZeroExt.fstHom k k k).toRingHom) =
          W.map (TrivSqZeroExt.fstHom k k k).toRingHom),
        ∃ (Z : Scheme) (e : Z ⟶ projModelCR Wq.toProjective)
          (v : Z ⟶ projModelCR (W.map (TrivSqZeroExt.fstHom k k k).toRingHom).toProjective),
          Epi v ∧
          e ≫ Vq = v ≫ Proj.map φ hφ ∧
          e ≫ g = v ≫ eqToHom (congrArg projModelCR (congrArg WeierstrassCurve.toProjective hW')).symm ≫ Proj.map φ' hφ') := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_hom_isFinite_flat_finrank_eq_of_map_map_eq_dualNumber.solution
