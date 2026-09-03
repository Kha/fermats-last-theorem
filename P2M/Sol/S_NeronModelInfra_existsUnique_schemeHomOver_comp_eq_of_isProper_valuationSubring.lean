import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
namespace P2MW.S_NeronModelInfra_existsUnique_schemeHomOver_comp_eq_of_isProper_valuationSubring

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace E1aAux

theorem existsUnique_lift_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : IsProper f]
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (i₁ : Spec (.of K) ⟶ X) (i₂ : Spec (.of R) ⟶ Y)
    (h : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i₂) :
    ∃! l : Spec (.of R) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = i₁ ∧ l ≫ f = i₂ := by
  have hP : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) f := by
    rw [← IsProper.eq_valuativeCriterion]; exact hf
  have hV : ValuativeCriterion f := hP.1.1.1
  let S : ValuativeCommSq f :=
    { R := R, K := K, i₁ := i₁, i₂ := i₂, commSq := ⟨h⟩ }
  obtain ⟨hU⟩ := hV S
  refine ⟨(default : S.commSq.LiftStruct).l, ⟨(default : S.commSq.LiftStruct).fac_left,
    (default : S.commSq.LiftStruct).fac_right⟩, ?_⟩
  rintro l' ⟨h1, h2⟩
  have : (CommSq.LiftStruct.mk l' h1 h2 : S.commSq.LiftStruct) = default := Unique.eq_default _
  exact congrArg CommSq.LiftStruct.l this

end E1aAux

theorem solution
    {L : Type u} [Field L] (O : ValuationSubring L)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (s : Spec (CommRingCat.of ↥O) ⟶ Y) (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype) ≫ s) :
    ∃! xt : SchemeHomOver s f, Spec.map (CommRingCat.ofHom O.subtype) ≫ xt.1 = x := by
  have h : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (↥O) L)) ≫ s := hx
  obtain ⟨l, ⟨hl1, hl2⟩, huniq⟩ := E1aAux.existsUnique_lift_of_isProper f (↥O) L x s h
  refine ⟨⟨l, hl2⟩, hl1, ?_⟩
  intro Pt hPt
  exact Subtype.ext (huniq Pt.1 ⟨hPt, Pt.2⟩)
