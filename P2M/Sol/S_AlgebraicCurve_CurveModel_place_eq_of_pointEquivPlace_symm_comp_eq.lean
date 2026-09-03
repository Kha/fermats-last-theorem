import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
namespace P2MW.S_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u v

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (𝔐 : AlgebraicCurve.CurveModel K L)
    {X B : Scheme.{u}} (πX : X ⟶ B) (s : Spec (CommRingCat.of K) ⟶ B)
    (e : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX s) (he : IsIso e)
    (he_snd : e ≫ CategoryTheory.Limits.pullback.snd πX s = 𝔐.toBase)
    (P Q : Place K L)
    (h : (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s =
      (𝔐.pointEquivPlace.symm Q).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s) :
    P = Q := by
  have h2 : (𝔐.pointEquivPlace.symm P).1 ≫ e = (𝔐.pointEquivPlace.symm Q).1 ≫ e := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · simpa only [Category.assoc] using h
    · rw [Category.assoc, he_snd, (𝔐.pointEquivPlace.symm P).2, Category.assoc, he_snd, (𝔐.pointEquivPlace.symm Q).2]
  haveI := he
  have h3 : (𝔐.pointEquivPlace.symm P).1 = (𝔐.pointEquivPlace.symm Q).1 := (cancel_mono e).mp h2
  exact 𝔐.pointEquivPlace.symm.injective (Subtype.ext h3)
