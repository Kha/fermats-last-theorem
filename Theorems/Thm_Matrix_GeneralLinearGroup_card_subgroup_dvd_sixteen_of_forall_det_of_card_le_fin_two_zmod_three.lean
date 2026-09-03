import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three

theorem Matrix.GeneralLinearGroup.card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    (hirr : ¬ ∃ v : Fin 2 → ZMod 3, v ≠ 0 ∧ ∀ h ∈ H, ∃ c : ZMod 3,
      Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) (ZMod 3)) v = c • v)
    (hdet : ∀ d : (ZMod 3)ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = d)
    (hle : Nat.card H ≤ 24) :
    Nat.card H ∣ 16 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_GeneralLinearGroup_card_subgroup_dvd_sixteen_of_forall_det_of_card_le_fin_two_zmod_three.solution
