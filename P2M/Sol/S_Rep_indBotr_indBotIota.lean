import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_indBotIota_apply
import Theorems.Thm_Rep_indBotr_indBotMk
import P2M.Util
namespace P2MW.S_Rep_indBotr_indBotIota

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (a : A) :
    A.indBotr ((Rep.indBotι A).hom a) = a := by
  classical
  rw [Rep.indBotIota_apply, map_sum, Finset.sum_eq_single (1 : G)]
  · rw [Rep.indBotr_indBotMk, Finsupp.single_eq_same, one_smul, map_one, Module.End.one_apply]
  · intro g _ hg
    rw [Rep.indBotr_indBotMk, Finsupp.single_apply, if_neg hg, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h
