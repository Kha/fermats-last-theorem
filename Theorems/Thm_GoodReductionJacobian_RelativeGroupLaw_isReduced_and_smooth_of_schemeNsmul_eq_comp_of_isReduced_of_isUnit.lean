import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
attribute [-simp] GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit
    {k : Type u} [Field k] [PerfectField k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    (m : ℕ) (hm : IsUnit (m : k))
    {Z : Scheme.{u}} [IsReduced Z] (h : G ⟶ Z) (ι : Z ⟶ G)
    (hfac : h ≫ ι = L.schemeNsmul m) :
    IsReduced G ∧ Smooth g := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isReduced_and_smooth_of_schemeNsmul_eq_comp_of_isReduced_of_isUnit.solution
