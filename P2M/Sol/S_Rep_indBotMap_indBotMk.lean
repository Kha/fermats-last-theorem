import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import P2M.Util
namespace P2MW.S_Rep_indBotMap_indBotMk

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

theorem solution {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (φ : A ⟶ B) (g : G) (a : A) :
    (Rep.indBotMap φ).hom (A.indBotMk g a) = B.indBotMk g (φ.hom a) := by
  rfl
