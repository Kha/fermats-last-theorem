import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm

set_option autoImplicit false

theorem Subgroup.exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm {G : Type*} [Group G] {V : Type*} [CommGroup V] (π : G →* V) (hZ : π.ker ≤ Subgroup.center G) (hsq : ∀ z ∈ π.ker, ∃ w ∈ π.ker, w * w = z) (H : Subgroup V) (hH : ∀ h ∈ H, h * h = 1) (hlift : ∀ h ∈ H, ∃ g : G, π g = h) (hcomm : ∀ g g' : G, π g ∈ H → π g' ∈ H → g * g' = g' * g) : ∃ K : Subgroup G, (∀ g ∈ K, ∀ g' ∈ K, π g = π g' → g = g') ∧ ∀ v : V, (∃ g ∈ K, π g = v) ↔ v ∈ H := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_subgroup_injOn_map_eq_of_ker_le_center_of_comm.solution
