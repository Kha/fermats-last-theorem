import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_existsUnique_hom_comp_eq_specMap_and_specMap_comp_eq_of_isProper_of_valuationSubring

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {K : Type u} [Field K] (A : ValuationSubring K)
    (ρ : R →+* ↥A)
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ)) :
    ∃! s : Spec (CommRingCat.of ↥A) ⟶ X,
      s ≫ f = Spec.map (CommRingCat.ofHom ρ) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by
  have hval : ValuativeCriterion f := by
    have h := congrFun (congrFun (congrFun AlgebraicGeometry.IsProper.eq_valuativeCriterion X) (Spec (CommRingCat.of R))) f
    have hP : IsProper f := inferInstance
    rw [h] at hP
    exact hP.1.1.1
  have hsq : CommSq x (Spec.map (CommRingCat.ofHom (algebraMap ↥A K))) f (Spec.map (CommRingCat.ofHom ρ)) := ⟨hx⟩
  let S : ValuativeCommSq f :=
    { R := ↥A, K := K, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨huniq⟩ := hval S
  let l := (default : S.commSq.LiftStruct)
  refine ⟨l.l, ⟨l.fac_right, l.fac_left⟩, ?_⟩
  rintro s ⟨hs₁, hs₂⟩
  have : (⟨s, hs₂, hs₁⟩ : S.commSq.LiftStruct) = l := Subsingleton.elim _ _
  exact congrArg CommSq.LiftStruct.l this

