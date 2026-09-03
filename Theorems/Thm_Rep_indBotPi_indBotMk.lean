import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_indBotPi_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.indBotPi_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g : G) (a : A) :
    (Rep.indBotπ A).hom (A.indBotMk g a) = A.ρ g⁻¹ a := by p2m_exact_reverting @_root_.P2MW.S_Rep_indBotPi_indBotMk.solution
