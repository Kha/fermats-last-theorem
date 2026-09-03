import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_subsingleton_tateH0_ind_bot
import Theorems.Thm_Rep_subsingleton_tateHneg1_ind_bot
import P2M.Util
namespace P2MW.S_Rep_isZero_tateCohomology_indBot

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (q : ℤ) :
    CategoryTheory.Limits.IsZero (A.indBot.tateCohomology q) := by
  classical
  let B : Rep.{u} k (⊥ : Subgroup G) := Rep.res (⊥ : Subgroup G).subtype A
  rcases q with (_ | n) | (_ | n)
  ·
    show CategoryTheory.Limits.IsZero (ModuleCat.of k A.indBot.tateH0)
    haveI : Subsingleton A.indBot.tateH0 := Rep.subsingleton_tateH0_ind_bot B
    exact ModuleCat.isZero_of_subsingleton _
  ·
    show CategoryTheory.Limits.IsZero (groupCohomology A.indBot (n + 1))
    refine (isZero_groupCohomology_succ_of_subsingleton B n).of_iso ?_
    exact (groupCohomology.functor k G (n + 1)).mapIso (Rep.indCoindIso B) ≪≫ groupCohomology.coindIso B (n + 1)
  ·
    show CategoryTheory.Limits.IsZero (ModuleCat.of k A.indBot.tateHneg1)
    haveI : Subsingleton A.indBot.tateHneg1 := Rep.subsingleton_tateHneg1_ind_bot B
    exact ModuleCat.isZero_of_subsingleton _
  ·
    show CategoryTheory.Limits.IsZero (groupHomology A.indBot (n + 1))
    exact (isZero_groupHomology_succ_of_subsingleton B n).of_iso (groupHomology.indIso (⊥ : Subgroup G) B (n + 1))
