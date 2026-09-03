import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_comap_torsionIdeal_eq_comap_ker_one

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3200000 in
theorem solution
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ)
    {Y : Scheme.{u}} (γ : Y ⟶ projModelCR W) :
    (torsionIdeal G q).comap (γ ≫ toPullbackId) =
      (Scheme.Hom.ker (G.one (𝟙 _)).1).comap (γ ≫ G.schemeNsmul q) := by
  haveI hsep : IsSeparated (projModelStrCR W.toProjective) := by unfold projModelStrCR; infer_instance
  haveI hO : IsClosedImmersion (G.one (𝟙 _)).1 := by
    have : IsClosedImmersion ((G.one (𝟙 _)).1 ≫ projModelStrCR W.toProjective) := by
      rw [(G.one (𝟙 _)).2]; infer_instance
    exact .of_comp _ (projModelStrCR W.toProjective)

  have htP : (toPullbackId (W := W.toProjective)) ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  haveI : IsIso (toPullbackId (W := W.toProjective)) :=
    isIso_of_comp_hom_eq_id (pullback.fst (projModelStrCR W.toProjective) (𝟙 (base (T := T)))) htP

  unfold torsionIdeal
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

  have hcond : pullback.fst (γ ≫ G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ γ ≫ toPullbackId =
      pullback.lift (pullback.fst (γ ≫ G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ γ) (pullback.snd (γ ≫ G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1)
          (by rw [Category.assoc]; exact pullback.condition) ≫
        pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ toPullbackId := by
    rw [← Category.assoc, ← Category.assoc, pullback.lift_fst]
  have hPB : IsPullback (pullback.fst (γ ≫ G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1)
      (pullback.lift (pullback.fst (γ ≫ G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ γ) (pullback.snd (γ ≫ G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1)
        (by rw [Category.assoc]; exact pullback.condition))
      (γ ≫ toPullbackId) (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1 ≫ toPullbackId) := by
    refine IsPullback.of_isLimit' ⟨hcond⟩ (PullbackCone.IsLimit.mk hcond
      (fun s ↦ pullback.lift s.fst (s.snd ≫ pullback.snd (G.schemeNsmul q) (G.one (𝟙 (base (T := T)))).1) ?_) ?_ ?_ ?_)
    · have h := s.condition
      rw [← Category.assoc, ← Category.assoc] at h
      have h' := (cancel_mono toPullbackId).mp h
      rw [← Category.assoc, h', Category.assoc, pullback.condition, Category.assoc]
    · intro s; exact pullback.lift_fst _ _ _
    · intro s
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
        have h := s.condition
        rw [← Category.assoc, ← Category.assoc] at h
        exact (cancel_mono toPullbackId).mp h
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    · intro s m h1 h2
      apply pullback.hom_ext
      · rw [pullback.lift_fst]; exact h1
      · rw [pullback.lift_snd, ← h2, Category.assoc, pullback.lift_snd]
  rw [← hPB.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso]
