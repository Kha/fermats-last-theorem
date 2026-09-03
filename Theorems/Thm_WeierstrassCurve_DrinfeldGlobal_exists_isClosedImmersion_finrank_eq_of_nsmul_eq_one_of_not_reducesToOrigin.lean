import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_of_nsmul_eq_one_of_not_reducesToOrigin

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal
attribute [local instance] MvPolynomial.gradedAlgebra
open IsLocalRing in

theorem WeierstrassCurve.DrinfeldGlobal.exists_isClosedImmersion_finrank_eq_of_nsmul_eq_one_of_not_reducesToOrigin
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [IsLocalRing T] [Algebra A T] (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (P : Section W.toProjective)
    (hPq : (𝒢 T W hΔ).nsmul (𝟙 _) q P = (𝒢 T W hΔ).one (𝟙 _))
    (hP0 : ∀ χ : OriginChartRing W.toProjective →+* T, ¬ ReducesToOrigin P χ (maximalIdeal T)) :
    ∃ (K : Scheme) (ι : K ⟶ projModelCR W.toProjective),
      IsClosedImmersion ι ∧
      IsFinite (ι ≫ projModelStrCR W.toProjective) ∧ Flat (ι ≫ projModelStrCR W.toProjective) ∧
      LocallyOfFinitePresentation (ι ≫ projModelStrCR W.toProjective) ∧
      (∀ s, (ι ≫ projModelStrCR W.toProjective).finrank s = q) ∧
      (∀ i : ℕ, ∃ σ : Spec (CommRingCat.of T) ⟶ K, σ ≫ ι = ((𝒢 T W hΔ).nsmul (𝟙 _) i P).1) ∧
      (∀ (X : Scheme) (f g : projModelCR W.toProjective ⟶ X),
        (∀ i : ℕ, ((𝒢 T W hΔ).nsmul (𝟙 _) i P).1 ≫ f = ((𝒢 T W hΔ).nsmul (𝟙 _) i P).1 ≫ g) → ι ≫ f = ι ≫ g) ∧
      (∀ (Z : Scheme) (j : Z ⟶ projModelCR W.toProjective) [IsClosedImmersion j],
        (∀ i : ℕ, ∃ τ : Spec (CommRingCat.of T) ⟶ Z, τ ≫ j = ((𝒢 T W hΔ).nsmul (𝟙 _) i P).1) →
        ∃ κ : K ⟶ Z, κ ≫ j = ι) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isClosedImmersion_finrank_eq_of_nsmul_eq_one_of_not_reducesToOrigin.solution
