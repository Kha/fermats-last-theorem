import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import P2M.Util
import P2M.Sol.S_Rep_indBotMap_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory
theorem Rep.indBotMap_indBotMk {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (φ : A ⟶ B) (g : G) (a : A) :
    (Rep.indBotMap φ).hom (A.indBotMk g a) = B.indBotMk g (φ.hom a) := by p2m_exact_reverting @_root_.P2MW.S_Rep_indBotMap_indBotMk.solution
