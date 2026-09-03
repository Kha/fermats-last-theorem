import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import P2M.Util
import P2M.Sol.S_Rep_finite_H1_ihom_relationModuleInt
attribute [-simp] Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk Rep.coe_tateδneg2_apply

set_option autoImplicit false
open CategoryTheory

theorem Rep.finite_H1_ihom_relationModuleInt {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Fintype B] (E : Rep ℤ G)
    [Module.Finite ℤ E] : Finite (groupCohomology.H1 ((ihom (Rep.relationModuleInt B)).obj E)) := by p2m_exact_reverting @_root_.P2MW.S_Rep_finite_H1_ihom_relationModuleInt.solution
