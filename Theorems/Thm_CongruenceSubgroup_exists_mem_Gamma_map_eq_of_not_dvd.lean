import Mathlib
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups

theorem CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    (∀ g : SL(2, ZMod p), ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma N ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) γ = g) ∧
    (∀ γ : SL(2, ℤ), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod p)) γ = 1 ↔
        γ ∈ CongruenceSubgroup.Gamma p) ∧
    ((-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma1 N ↔ N ≤ 2) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd.solution
