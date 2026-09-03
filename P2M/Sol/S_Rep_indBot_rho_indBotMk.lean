import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import P2M.Util
namespace P2MW.S_Rep_indBot_rho_indBotMk

set_option autoImplicit false
universe u
open CategoryTheory Rep

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

theorem solution {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (g h : G) (a : A) :
    A.indBot.ρ g (A.indBotMk h a) = A.indBotMk (h * g⁻¹) a :=
  Representation.ind_mk _ _ g h a
