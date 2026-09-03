import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Theorems.Thm_Rep_exact_tateDelta0_map
import Theorems.Thm_Rep_exact_tateDeltaNeg1_tateH0Map
import Theorems.Thm_Rep_exact_tateDeltaNeg2_tateHneg1Map
import P2M.Util
namespace P2MW.S_Rep_exact_tateDelta_tateMap

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    Function.Exact (Rep.tateδ hX n).hom (Rep.tateMap X.f (n + 1)).hom := by
  match n with
  | Int.ofNat (m + 1) =>
    exact LinearMap.exact_iff.2
      (groupCohomology.mapShortComplex₁_exact hX (rfl : m + 1 + 1 = m + 2)).moduleCat_range_eq_ker.symm
  | Int.ofNat 0 => exact Rep.exact_tateDelta0_map hX
  | Int.negSucc 0 => exact Rep.exact_tateDeltaNeg1_tateH0Map hX
  | Int.negSucc 1 => exact Rep.exact_tateDeltaNeg2_tateHneg1Map hX
  | Int.negSucc (m + 2) =>
    exact LinearMap.exact_iff.2
      (groupHomology.mapShortComplex₁_exact hX (rfl : m + 1 + 1 = m + 2)).moduleCat_range_eq_ker.symm
