import Mathlib
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_dimShiftDown_shortExact
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Theorems.Thm_Rep_shortExact_map_tensorRight_of_splitting
import P2M.Util
namespace P2MW.S_Rep_shortExact_dimShiftDown_map_tensorRight

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

theorem solution {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G) :
    (A.dimShiftDown.map (MonoidalCategory.tensorRight B)).ShortExact := by
  exact Rep.shortExact_map_tensorRight_of_splitting (Rep.dimShiftDown_shortExact A) A.indBotσ
    (fun a => Rep.indBotPi_indBotSigma A a) B
