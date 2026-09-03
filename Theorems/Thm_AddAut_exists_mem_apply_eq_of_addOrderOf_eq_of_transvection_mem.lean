import Mathlib
import P2M.Util
import P2M.Sol.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
import Definitions.Def_Compat_Mathlib430

theorem AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
    (M : ℕ) [NeZero M] (H : Subgroup (AddAut (ZMod M × ZMod M)))
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    (ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M))
    (v w : ZMod M × ZMod M) (hv : addOrderOf v = M) (hw : addOrderOf w = M) :
    ∃ h ∈ H, h v = w := by p2m_exact_reverting @_root_.P2MW.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.solution
