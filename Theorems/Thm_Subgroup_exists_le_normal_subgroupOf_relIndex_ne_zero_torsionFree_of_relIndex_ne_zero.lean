import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero

set_option autoImplicit false

theorem Subgroup.exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero
    {G : Type} [Group G] (H K N₀ : Subgroup G) (hHK : H ≤ K) (hHidx : H.relIndex K ≠ 0)
    (hN₀ : N₀ ≤ H) (hN₀idx : N₀.relIndex H ≠ 0) (htf : ∀ g ∈ N₀, IsOfFinOrder g → g = 1) :
    ∃ N : Subgroup G, N ≤ N₀ ∧ (N.subgroupOf K).Normal ∧ N.relIndex H ≠ 0 ∧ ∀ g ∈ N, IsOfFinOrder g → g = 1 := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_le_normal_subgroupOf_relIndex_ne_zero_torsionFree_of_relIndex_ne_zero.solution
