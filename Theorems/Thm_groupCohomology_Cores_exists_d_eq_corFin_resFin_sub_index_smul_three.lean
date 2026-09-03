import Mathlib
import Definitions.Def_GroupCohomology_CorestrictionFin
import P2M.Util
import P2M.Sol.S_groupCohomology_Cores_exists_d_eq_corFin_resFin_sub_index_smul_three

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology groupCohomology.Cores

theorem groupCohomology.Cores.exists_d_eq_corFin_resFin_sub_index_smul_three
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex]
    (τ : Transversal H) (u : (Fin 3 → G) → A)
    (hu : ((inhomogeneousCochains A).d 3 4).hom u = 0) :
    ∃ b : (Fin 2 → G) → A,
      ((inhomogeneousCochains A).d 2 3).hom b = corFin A τ 3 (resFin A 3 u) - H.index • u ∧
      ∀ U : Subgroup G, U.Normal → U ≤ H → IsSlotInvariant U u → IsSlotInvariant U b := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Cores_exists_d_eq_corFin_resFin_sub_index_smul_three.solution
