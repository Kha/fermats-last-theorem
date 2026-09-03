import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_exact_tateH0Map_tateDelta0
import Theorems.Thm_Rep_exact_tateHneg1Map_tateDeltaNeg1
import Theorems.Thm_Rep_exact_map_tateDeltaNeg2
import P2M.Util
namespace P2MW.S_Rep_exact_tateMap_tateDelta

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateMap X.g n).hom (Rep.tateδ hX n).hom := by
  match n with
  | Int.ofNat (m + 1) =>
    exact LinearMap.exact_iff.2
      (groupCohomology.mapShortComplex₃_exact hX (rfl : m + 1 + 1 = m + 2)).moduleCat_range_eq_ker.symm
  | Int.ofNat 0 => exact Rep.exact_tateH0Map_tateDelta0 hX
  | Int.negSucc 0 => exact Rep.exact_tateHneg1Map_tateDeltaNeg1 hX
  | Int.negSucc 1 => exact Rep.exact_map_tateDeltaNeg2 hX
  | Int.negSucc (m + 2) =>
    exact LinearMap.exact_iff.2
      (groupHomology.mapShortComplex₃_exact hX (rfl : m + 1 + 1 = m + 2)).moduleCat_range_eq_ker.symm
