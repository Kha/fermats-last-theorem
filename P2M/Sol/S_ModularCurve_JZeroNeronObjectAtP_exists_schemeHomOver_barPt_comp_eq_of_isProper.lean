import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : baseRing p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    {X : Scheme.{0}} (f : X ⟶ base p) [IsProper f] (x : SchemeHomOver (genPt p) f) :
    ∃ xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, barPt A ≫ xA.1 = x.1 := by

  have hE : ValuativeCriterion.Existence f := by
    have hUC : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hUC
    exact hUC.1

  have hsq : x.1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (↥A) (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hρ.symm
  let S : ValuativeCommSq f :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := x.1, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := ⟨hsq⟩ }
  haveI : S.commSq.HasLift := hE S
  exact ⟨⟨S.commSq.lift, S.commSq.fac_right⟩, S.commSq.fac_left⟩
