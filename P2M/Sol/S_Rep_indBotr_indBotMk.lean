import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
namespace P2MW.S_Rep_indBotr_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    A.indBotr (A.indBotMk g a) = (Finsupp.single g (1 : k)) 1 • a := by
  simp [Rep.indBotr, Rep.indBotMk]
