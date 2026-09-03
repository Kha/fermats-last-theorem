import Mathlib
import Definitions.Def_GroupCohomology_CorestrictionFin
import P2M.Util
import P2M.Sol.S_groupCohomology_Cores_corFin_d

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology groupCohomology.Cores

theorem groupCohomology.Cores.corFin_d
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    (τ : Transversal H) (n : ℕ) (u : (Fin n → H) → A) :
    corFin A τ (n + 1) (((inhomogeneousCochains (Rep.res H.subtype A)).d n (n + 1)).hom u)
      = ((inhomogeneousCochains A).d n (n + 1)).hom (corFin A τ n u) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Cores_corFin_d.solution
