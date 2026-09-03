import Mathlib.GroupTheory.Finiteness
import P2M.Util
import P2M.Sol.S_AddSubgroup_addGroup_fg_of_le_of_addGroup_fg

theorem AddSubgroup.addGroup_fg_of_le_of_addGroup_fg {A : Type} [AddCommGroup A] {H₁ H₂ : AddSubgroup A}
    (hle : H₁ ≤ H₂) (hfg : AddGroup.FG ↥H₂) : AddGroup.FG ↥H₁ := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_addGroup_fg_of_le_of_addGroup_fg.solution
