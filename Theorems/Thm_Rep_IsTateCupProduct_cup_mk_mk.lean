import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import P2M.Util
import P2M.Sol.S_Rep_IsTateCupProduct_cup_mk_mk

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.IsTateCupProduct.cup_mk_mk {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (c : (A ⊗ B).ρ.invariants)
    (hc : (c : (A ⊗ B : Rep.{u} k G)) = (a : A) ⊗ₜ[k] (b : B)) :
    cup A B 0 0 0 (add_zero 0) (Submodule.Quotient.mk a : A.tateH0) (Submodule.Quotient.mk b : B.tateH0)
      = (Submodule.Quotient.mk c : (A ⊗ B).tateH0) := by p2m_exact_reverting @_root_.P2MW.S_Rep_IsTateCupProduct_cup_mk_mk.solution
