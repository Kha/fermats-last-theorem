import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import P2M.Util
import P2M.Sol.S_groupCohomology_Cores_map_cores_eq_cores_map

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.Cores.map_cores_eq_cores_map
    {k G : Type} [CommRing k] [Group G] (A B : Rep.{0} k G) (φ : A ⟶ B)
    (K : Subgroup G) [K.FiniteIndex] (τ : Cores.Transversal K) (z : groupCohomology (Rep.res K.subtype A) 2) :
    (groupCohomology.map (MonoidHom.id G) φ 2).hom (Cores.cores A τ z) =
      Cores.cores B τ ((groupCohomology.map (MonoidHom.id ↥K) ((Rep.resFunctor K.subtype).map φ) 2).hom z) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Cores_map_cores_eq_cores_map.solution
