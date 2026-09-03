import Mathlib
import P2M.Util
import P2M.Sol.S_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul
attribute [-simp] ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL
set_option autoImplicit false

open scoped MatrixGroups

theorem CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul (a b c : ℕ) (h0 : 0 < a + b + c)
    (h₁ : 24 ∣ a + 2 * b + 4 * c) (h₂ : 24 ∣ 4 * a + 2 * b + c) (hb : Even b) (h4 : 4 ∣ a + b + c) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 4) (((a + b + c) / 2 : ℕ) : ℤ),
      ∀ z : UpperHalfPlane, f z = ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b *
        ModularForm.eta (4 * (z : ℂ)) ^ c := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul.solution
