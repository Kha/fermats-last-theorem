import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_ExtendsToPlace_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve.JZeroNeronObjectAtP

theorem solution
    {p : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ)) (σA : Spec (CommRingCat.of ↥A) ⟶ base p)
    (hσA : barPt A ≫ σA = genPt p)
    {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f) :
    ExtendsToPlace A σA (L.one (genPt p)) := by
  refine ⟨L.one σA, ?_⟩
  have := congrArg Subtype.val (L.one_natural σA (genPt p) (barPt A) hσA)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at this
  exact this.symm
