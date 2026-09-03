import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (LG : RelativeGroupLaw k g) (hcG : LG.IsCommutative)
    {H : Scheme.{u}} {h : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType h] [IsReduced H]
    (LH : RelativeGroupLaw k h)
    (p : SchemeHomOver g h) [IsProper p.1]
    (hp : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LG.mul t x y) p =
        LH.mul t (NeronModelInfra.schemeHomOverComp x p) (NeronModelInfra.schemeHomOverComp y p))
    (hbij : Function.Bijective fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g =>
      NeronModelInfra.schemeHomOverComp x p) :
    IsIso p.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isIso_of_isProper_of_bijective_schemeHomOverComp_of_charZero.solution
