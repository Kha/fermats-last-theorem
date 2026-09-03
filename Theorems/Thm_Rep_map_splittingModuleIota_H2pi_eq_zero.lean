import Mathlib
import Definitions.Def_GroupCohomology_SplittingModule
import P2M.Util
import P2M.Sol.S_Rep_map_splittingModuleIota_H2pi_eq_zero

set_option autoImplicit false
universe u
open CategoryTheory Rep
theorem Rep.map_splittingModuleIota_H2pi_eq_zero {k G : Type u} [CommRing k] [Group G]
    (C : Rep.{u} k G) (φ : groupCohomology.cocycles₂ C) :
    ((groupCohomology.functor k G 2).map (Rep.splittingModuleι C φ)).hom (groupCohomology.H2π C φ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Rep_map_splittingModuleIota_H2pi_eq_zero.solution
