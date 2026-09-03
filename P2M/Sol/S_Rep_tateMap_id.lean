import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
namespace P2MW.S_Rep_tateMap_id

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep.{u} k G) (n : ℤ) :
    Rep.tateMap (𝟙 A) n = 𝟙 (A.tateCohomology n) := by
  match n with
  | Int.ofNat (m + 1) => exact groupCohomology.map_id (m + 1)
  | Int.ofNat 0 =>
    show ModuleCat.ofHom (Rep.tateH0Map (𝟙 A)) = _
    rw [Rep.tateH0Map_id]
    rfl
  | Int.negSucc 0 =>
    show ModuleCat.ofHom (Rep.tateHneg1Map (𝟙 A)) = _
    rw [Rep.tateHneg1Map_id]
    rfl
  | Int.negSucc (m + 1) => exact groupHomology.map_id (m + 1)
