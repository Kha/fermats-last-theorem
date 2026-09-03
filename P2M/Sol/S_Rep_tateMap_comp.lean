import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import P2M.Util
namespace P2MW.S_Rep_tateMap_comp

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem solution {k G : Type u} [CommRing k] [Group G] [Fintype G] {A B C : Rep.{u} k G}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℤ) :
    Rep.tateMap (φ ≫ ψ) n = Rep.tateMap φ n ≫ Rep.tateMap ψ n := by
  match n with
  | Int.ofNat (m + 1) => exact (groupCohomology.functor k G (m + 1)).map_comp φ ψ
  | Int.ofNat 0 =>
    show ModuleCat.ofHom (Rep.tateH0Map (φ ≫ ψ)) = ModuleCat.ofHom (Rep.tateH0Map φ) ≫ ModuleCat.ofHom (Rep.tateH0Map ψ)
    rw [Rep.tateH0Map_comp, ModuleCat.ofHom_comp]
  | Int.negSucc 0 =>
    show ModuleCat.ofHom (Rep.tateHneg1Map (φ ≫ ψ)) = ModuleCat.ofHom (Rep.tateHneg1Map φ) ≫ ModuleCat.ofHom (Rep.tateHneg1Map ψ)
    rw [Rep.tateHneg1Map_comp, ModuleCat.ofHom_comp]
  | Int.negSucc (m + 1) => exact (groupHomology.functor k G (m + 1)).map_comp φ ψ
