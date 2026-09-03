import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_bijective_tateDelta_of_isZero
import Theorems.Thm_Rep_isZero_tateCohomology_indBot
import P2M.Util
namespace P2MW.S_Rep_bijective_tateDelta_dimShiftDown

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep.{u} k G) (hA : A.dimShiftDown.ShortExact) (n : ℤ) :
    Function.Bijective (Rep.tateδ hA n).hom :=
  Rep.bijective_tateDelta_of_isZero hA n (Rep.isZero_tateCohomology_indBot A n) (Rep.isZero_tateCohomology_indBot A (n + 1))
