import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
namespace P2MW.S_AlgebraicCurve_CurveModel_isRational_pointEquivPlace

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u v

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L)
    (x : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    (M.pointEquivPlace x).IsRational := by
  classical
  letI := M.functionFieldAlgebra
  have hff : ∀ a : K, M.ffEquiv (algebraMap K L a) = algebraMap K M.C.functionField a := M.ffEquiv_algebraMap

  have hrat' : (AlgebraicCurve.Place.congrRingEquiv M.ffEquiv hff (M.pointEquivPlace x)).IsRational := by
    refine AlgebraicCurve.Place.isRational_of_range_stalk_section_eq M.toBase x.1 x.2
      (AlgebraicCurve.Place.congrRingEquiv M.ffEquiv hff (M.pointEquivPlace x)) ?_
    rw [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring]
    have h := M.range_stalk_eq (pointEquivClosedPoint M.toBase x)
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      show M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.pointEquivPlace x).toValuationSubring
      have : M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.placeOfPoint (pointEquivClosedPoint M.toBase x)).toValuationSubring.toSubring :=
        h ▸ ⟨s, rfl⟩
      exact this
    · intro hg
      have hg' : M.ffEquiv.symm g ∈ (M.placeOfPoint (pointEquivClosedPoint M.toBase x)).toValuationSubring.toSubring := hg
      rw [← h] at hg'
      obtain ⟨s, hs⟩ := hg'
      refine ⟨s, M.ffEquiv.symm.injective ?_⟩
      exact hs

  intro r
  obtain ⟨a, ha⟩ := hrat' (AlgebraicCurve.Place.congrResidueAlgEquiv M.ffEquiv hff (M.pointEquivPlace x) r)
  refine ⟨a, (AlgebraicCurve.Place.congrResidueAlgEquiv M.ffEquiv hff (M.pointEquivPlace x)).injective ?_⟩
  rw [AlgEquiv.commutes]
  exact ha
