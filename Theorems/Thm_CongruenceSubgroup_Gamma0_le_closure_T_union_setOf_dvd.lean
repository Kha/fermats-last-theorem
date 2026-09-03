import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd

theorem CongruenceSubgroup.Gamma0_le_closure_T_union_setOf_dvd (M : ℕ) {q : ℕ} (hq : q ≠ 0) :
    CongruenceSubgroup.Gamma0 M ≤ Subgroup.closure
      ({ModularGroup.T} ∪ {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ |
        (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1}) := by p2m_exact_reverting @_root_.P2MW.S_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd.solution
