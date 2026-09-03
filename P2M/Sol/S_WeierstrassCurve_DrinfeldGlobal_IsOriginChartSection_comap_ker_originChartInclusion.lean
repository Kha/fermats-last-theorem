import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsOriginChartSection_comap_ker_originChartInclusion

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hP : IsOriginChartSection P χ) :
    (Scheme.Hom.ker P.1).comap (originChartι W) = Scheme.Hom.ker (Spec.map (CommRingCat.ofHom χ)) := by
  haveI hsep : IsSeparated (projModelStrCR W.toProjective) := by unfold projModelStrCR; infer_instance
  haveI : IsClosedImmersion P.1 := by
    have : IsClosedImmersion (P.1 ≫ projModelStrCR W.toProjective) := by rw [P.2]; infer_instance
    exact .of_comp _ (projModelStrCR W.toProjective)

  have hsq : Spec.map (CommRingCat.ofHom χ) ≫ originChartι W = 𝟙 _ ≫ P.1 := by rw [Category.id_comp, hP]
  have hPB : IsPullback (Spec.map (CommRingCat.ofHom χ)) (𝟙 _) (originChartι W) P.1 := by
    refine IsPullback.of_isLimit' ⟨hsq⟩ (Limits.PullbackCone.IsLimit.mk hsq (fun s ↦ s.snd) ?_ ?_ ?_)
    · intro s
      rw [← cancel_mono (originChartι W), Category.assoc, hsq, Category.id_comp]
      exact s.condition.symm
    · intro s; exact Category.comp_id _
    · intro s m _ h2; simpa using h2
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← hPB.isoPullback_inv_fst,
    Scheme.Hom.ker_comp_of_isIso]
