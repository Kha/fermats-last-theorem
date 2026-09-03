import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
import P2M.Sol.S_Rep_indBot_rho_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.indBot_rho_indBotMk {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g h : G) (a : A) :
    A.indBot.ρ g (A.indBotMk h a) = A.indBotMk (h * g⁻¹) a := by p2m_exact_reverting @_root_.P2MW.S_Rep_indBot_rho_indBotMk.solution
