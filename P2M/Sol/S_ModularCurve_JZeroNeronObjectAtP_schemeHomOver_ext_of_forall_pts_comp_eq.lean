import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_schemeHomOver_ext_of_forall_pts_comp_eq

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (ψ₁ ψ₂ : SchemeHomOver O.g Λ.f)
    (h : ∀ x : JZero (N₀ * p), (O.pts x).1 ≫ ψ₁.1 = (O.pts x).1 ≫ ψ₂.1) :
    ψ₁ = ψ₂ := by
  haveI : IsProper Λ.f := hΛ.1.proper
  haveI : Smooth O.g := O.smooth
  haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
  haveI : IsDiscreteValuationRing (baseRing p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsReduced O.G := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian O.g
  haveI : IsFractionRing (baseRing p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := baseRing p) ℚ (AlgebraicClosure ℚ) (gY := O.g) (gX := Λ.f) ψ₁ ψ₂ ?_
  intro z
  obtain ⟨x, rfl⟩ := O.pts.surjective z
  exact h x
