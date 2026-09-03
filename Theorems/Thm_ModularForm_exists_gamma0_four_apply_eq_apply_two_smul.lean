import Mathlib
import P2M.Util
import P2M.Sol.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul
set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.exists_gamma0_four_apply_eq_apply_two_smul {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 4) k,
      ∀ z : UpperHalfPlane, g z = f ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) • z) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exists_gamma0_four_apply_eq_apply_two_smul.solution
