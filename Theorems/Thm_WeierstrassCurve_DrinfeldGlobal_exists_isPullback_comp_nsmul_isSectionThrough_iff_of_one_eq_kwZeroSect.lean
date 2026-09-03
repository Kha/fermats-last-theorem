import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
attribute [-simp] WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.injEq WeierstrassCurve.DrinfeldGlobal.LevelTransport.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect
    {B T : Type} [CommRing B] [CommRing T] (V : WeierstrassCurve B) [V.IsElliptic] (f : B →+* T)
    (G : RelativeGroupLaw B (projModelStrCR V.toProjective)) (hG : (G.one (𝟙 _)).1 = (kwZeroSect B V).1)
    (L : RelativeGroupLaw T (projModelStrCR (V.map f).toProjective))
    (hL : (L.one (𝟙 _)).1 = (kwZeroSect T (V.map f)).1) :
    ∃ (Φ : projModelCR (V.map f).toProjective ⟶ projModelCR V.toProjective)
      (hsq : Φ ≫ projModelStrCR V.toProjective = projModelStrCR (V.map f).toProjective ≫ Spec.map (CommRingCat.ofHom f)),
      IsPullback Φ (projModelStrCR (V.map f).toProjective) (projModelStrCR V.toProjective)
        (Spec.map (CommRingCat.ofHom f)) ∧
      (∀ (n : ℕ) (S : Section (V.map f).toProjective),
        (L.nsmul (𝟙 _) n S).1 ≫ Φ =
          (G.nsmul (Spec.map (CommRingCat.ofHom f)) n
            ⟨S.1 ≫ Φ, by rw [Category.assoc, hsq, ← Category.assoc, S.2, Category.id_comp]⟩).1) ∧
      ((L.one (𝟙 _)).1 ≫ Φ = (G.one (Spec.map (CommRingCat.ofHom f))).1) ∧
      (∀ (S : Section (V.map f).toProjective) (x y : T),
        IsSectionThrough S x y ↔
          ∃ χ : ZChartRing V.toProjective →+* T, S.1 ≫ Φ = Spec.map (CommRingCat.ofHom χ) ≫ zChartι V.toProjective ∧
            χ (xOverZ V.toProjective) = x ∧ χ (yOverZ V.toProjective) = y) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_isPullback_comp_nsmul_isSectionThrough_iff_of_one_eq_kwZeroSect.solution
