import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_existsUnique_schemeHomOver_barPt_comp_eq_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem solution
    {p : ℕ} {X : Scheme.{0}} (f : X ⟶ base p) [IsProper f]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ρ : baseRing p →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    (pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X) (hpt : pt ≫ f = genPt p) :
    ∃! s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, barPt A ≫ s.1 = pt := by
  have hVC : ValuativeCriterion f := by
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) f := by
      rw [← IsProper.eq_valuativeCriterion]; infer_instance
    exact h.1.1.1
  have halg : (algebraMap ↥A (AlgebraicClosure ℚ)) = A.subtype := rfl
  have hsq : CommSq pt (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) f
      (Spec.map (CommRingCat.ofHom ρ)) := by
    constructor
    rw [hpt, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halg, hρ]
  let S : ValuativeCommSq f :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := pt, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨hU⟩ := hVC S
  let Ls : hsq.LiftStruct := (default : S.commSq.LiftStruct)
  refine ⟨⟨Ls.l, Ls.fac_right⟩, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom A.subtype) ≫ Ls.l = pt
    rw [← halg]; exact Ls.fac_left
  · rintro ⟨s, hs⟩ hs'
    have hL' : (⟨s, (by show Spec.map (CommRingCat.ofHom A.subtype) ≫ s = pt; exact hs'), hs⟩ : S.commSq.LiftStruct) = Ls :=
      Subsingleton.elim _ _
    exact Subtype.ext (congrArg CommSq.LiftStruct.l hL')
