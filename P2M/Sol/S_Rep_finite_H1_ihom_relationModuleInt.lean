import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Theorems.Thm_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int
import Theorems.Thm_Rep_moduleFinite_relationCarrier
import Theorems.Thm_Rep_moduleFree_relationCarrier
import P2M.Util
namespace P2MW.S_Rep_finite_H1_ihom_relationModuleInt

set_option autoImplicit false
open CategoryTheory

namespace Rep
p2m_export "Rep" "V free of ρ hV2 hV1 Hom relationCarrier relationModuleInt moduleFinite_relationCarrier moduleFree_relationCarrier"
namespace K4
p2m_open "Rep"

theorem moduleFinite_ihom_relationModuleInt {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Fintype B] (E : Rep ℤ G)
    [hE : Module.Finite ℤ E] : Module.Finite ℤ ((ihom (Rep.relationModuleInt B)).obj E) := by
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Module.Finite ℤ (Rep.relationCarrier B) := Rep.moduleFinite_relationCarrier B
  haveI : Module.Free ℤ (Rep.relationCarrier B) := Rep.moduleFree_relationCarrier B

  cases E
  rename_i V hV1 hV2 ρ
  have h2 : hV2 = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  subst h2

  have key : Module.Finite ℤ (Rep.relationCarrier B →ₗ[ℤ] V) := Module.Finite.linearMap ℤ ℤ _ _

  convert key using 1
  rfl
  rfl
  rfl

end Rep.K4

theorem solution {G : Type} [Group G] [Finite G] (B : Rep ℤ G) [Fintype B] (E : Rep ℤ G)
    [Module.Finite ℤ E] : Finite (groupCohomology.H1 ((ihom (Rep.relationModuleInt B)).obj E)) := by
  haveI := Rep.K4.moduleFinite_ihom_relationModuleInt B E
  exact groupCohomology.finite_groupCohomology_succ_of_moduleFinite_int ((ihom (Rep.relationModuleInt B)).obj E) 0
